; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(%interactive)


(%autoprove alternate-trichotomy-of-symbol-<)

(%autoprove all-equalp-removal
            (%cdr-induction x)
            (%restrict default repeat (equal n '(+ '1 (len (cdr x))))))



(%autoadmit rw.leading-symbol)

(encapsulate
 ()
 (local (%disable default consp-when-consp-of-cdr-cheap))  ;; BOZO screws with our stupid elim heuristics
 (%defprojection :list (rw.leading-symbol-list x)
                 :element (rw.leading-symbol x)
                 :nil-preservingp t))

(%autoprove forcing-symbolp-of-rw.leading-symbol
            (%enable default rw.leading-symbol))

(%autoprove forcing-symbol-listp-of-rw.leading-symbol-list
            (%cdr-induction x))


(encapsulate
 ()
 (local (%disable default
                  memberp-when-not-consp
                  memberp-when-memberp-of-cdr
                  subsetp-when-not-consp
                  not-in-subset-when-not-in-superset-one
                  in-superset-when-in-subset-two
                  symbolp-when-logic.function-namep
                  symbolp-when-logic.variablep
                  same-length-prefixes-equal-cheap
                  expensive-arithmetic-rules
                  expensive-arithmetic-rules-two
                  type-set-like-rules
                  unusual-consp-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  formula-decomposition))

 (%defmap :map (rw.typed-rulemapp x)
          :key (symbolp x)
          :val (rw.rule-listp x)
          :key-list (symbol-listp x)
          :val-list (rw.rule-list-listp x)
          :val-of-nil t))





(%autoadmit rw.rule-list-consistent-leading-symbolsp)

(%autoprove rw.rule-list-consistent-leading-symbolsp-removal
            (%cdr-induction rules)
            (%restrict default rw.rule-list-consistent-leading-symbolsp (equal rules 'rules))
            (%disable default all-equalp-removal))

(%autoadmit rw.rulemap-consistent-leading-symbolsp)

(%autoprove rw.rulemap-consistent-leading-symbolsp-removal
            (%cdr-induction rulemap)
            (%restrict default rw.rulemap-consistent-leading-symbolsp (equal rulemap 'rulemap))
            (%disable default all-equalp-removal))



(defsection rw.theoryp
  (%autoadmit rw.theoryp)
  (%autoadmit rw.theory->name)
  (%autoadmit rw.theory->left)
  (%autoadmit rw.theory->right)
  (%autoadmit rw.theory->rulemap)
  (%autoadmit rw.theory)
  (local (%enable default
                  rw.theory
                  rw.theory->name
                  rw.theory->left
                  rw.theory->right
                  rw.theory->rulemap))
  (%autoprove booleanp-of-rw.theoryp
              (%restrict default rw.theoryp (equal x 'x)))
  (%autoprove consp-of-rw.theory)
  (%autoprove rw.theory-under-iff)
  (%autoprove forcing-rw.theoryp-of-rw.theory
              (%restrict default rw.theoryp
                         (equal x '(cons name (cons left (cons right (cons rulemap 'nil)))))))
  (%autoprove rw.theory->name-of-rw.theory)
  (%autoprove rw.theory->left-of-rw.theory)
  (%autoprove rw.theory->right-of-rw.theory)
  (%autoprove rw.theory->rulemap-of-rw.theory)
  (%autoprove forcing-symbolp-of-rw.theory->name
              (%restrict default rw.theoryp (equal x 'x)))
  (%autoprove forcing-theoryp-of-rw.theory->left
              (%restrict default rw.theoryp (equal x 'x)))
  (%autoprove forcing-theoryp-of-rw.theory->right
              (%restrict default rw.theoryp (equal x 'x)))
  (%autoprove forcing-rw.typed-rulemapp-of-rw.theory->rulemap
              (%restrict default rw.theoryp (equal x 'x)))
  (%autoprove forcing-leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.theory->rulemap
              (%restrict default rw.theoryp (equal x 'x))
              (%enable default all-equalp-removal)
              (%disable default
                        member-of-nonep-of-cdr-when-member-of-nonep
                        simple-flatten-when-not-consp
                        rw.rule-list-lhses-when-not-consp
                        rw.leading-symbol-list-when-not-consp))
  (%autoprove rank-of-rw.theory->left)
  (%autoprove rank-of-rw.theory->right)
  (%autoprove rw.theory->left-when-not-consp)
  (%autoprove rw.theory->right-when-not-consp))



(defsection rw.theory-atblp
  (%autoadmit rw.theory-atblp)
  (%autoprove booleanp-of-rw.theory-atblp
              (%autoinduct rw.theory-atblp)
              (%restrict default rw.theory-atblp (equal x 'x)))
  (%autoprove rw.theory-atblp-when-not-consp
              (%restrict default rw.theory-atblp (equal x 'x)))
  (%autoprove forcing-theory-atblp-of-rw.theory->left
              (%restrict default rw.theory-atblp (equal x 'x)))
  (%autoprove forcing-theory-atblp-of-rw.theory->right
              (%restrict default rw.theory-atblp (equal x 'x)))
  (%autoprove forcing-rw.rule-list-list-atblp-of-of-range-of-rw.theory->rulemap
              (%restrict default rw.theory-atblp (equal x 'x))
              (%enable default rw.theory->rulemap))
  (%autoprove forcing-rw.theory-atblp-of-rw.theory
              (%restrict default rw.theory-atblp (equal x '(rw.theory name left right rules)))))


(defsection rw.theory-env-okp
  (%autoadmit rw.theory-env-okp)
  (%autoprove booleanp-of-rw.theory-env-okp
              (%autoinduct rw.theory-env-okp)
              (%restrict default rw.theory-env-okp (equal x 'x)))
  (%autoprove rw.theory-env-okp-when-not-consp
              (%restrict default rw.theory-env-okp (equal x 'x)))
  (%autoprove forcing-theory-env-okp-of-rw.theory->left
              (%restrict default rw.theory-env-okp (equal x 'x)))
  (%autoprove forcing-theory-env-okp-of-rw.theory->right
              (%restrict default rw.theory-env-okp (equal x 'x)))
  (%autoprove forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory->rulemap
              (%restrict default rw.theory-env-okp (equal x 'x))
              (%enable default rw.theory->rulemap))
  (%autoprove forcing-rw.theory-env-okp-of-rw.theory
              (%restrict default rw.theory-env-okp (equal x '(rw.theory name left right rules)))))



(%autoprove rw.rule-list-atblp-of-simple-flatten
            (%cdr-induction x))

(%autoprove rw.rule-list-env-okp-of-simple-flatten
            (%cdr-induction x))

(defsection rw.theory-allrules
  (%autoadmit rw.fast-theory-all-rules)
  (%autoadmit rw.slow-theory-all-rules)
  (%autoadmit rw.theory-allrules)
  (%autoprove true-listp-of-rw.fast-theory-all-rules
              (%autoinduct rw.fast-theory-all-rules)
              (%restrict default rw.fast-theory-all-rules (equal x 'x)))
  (%autoprove lemma-for-definition-of-rw.theory-allrules
              (%autoinduct rw.fast-theory-all-rules)
              (%restrict default rw.fast-theory-all-rules (equal x 'x))
              (%restrict default rw.slow-theory-all-rules (equal x 'x)))
  (%autoprove definition-of-rw.theory-allrules
              (%enable default
                       rw.theory-allrules
                       lemma-for-definition-of-rw.theory-allrules)
              (%restrict default rw.slow-theory-all-rules (equal x 'x)))
  (%autoprove rw.fast-theory-all-rules-elim
              (%enable default
                       rw.theory-allrules
                       lemma-for-definition-of-rw.theory-allrules))
  (%autoprove forcing-true-listp-of-rw.theory-allrules
              (%restrict default definition-of-rw.theory-allrules (equal x 'x)))
  (%autoprove forcing-rw.rule-listp-of-rw.theory-allrules
              (%autoinduct rw.slow-theory-all-rules)
              (%restrict default definition-of-rw.theory-allrules (equal x 'x)))
  (%autoprove forcing-rw.rule-listp-atblp-of-rw.theory-allrules
              (%autoinduct rw.slow-theory-all-rules)
              (%restrict default definition-of-rw.theory-allrules (equal x 'x)))
  (%autoprove forcing-rw.rule-listp-env-okp-of-rw.theory-allrules
              (%autoinduct rw.slow-theory-all-rules)
              (%restrict default definition-of-rw.theory-allrules (equal x 'x))))


(defsection rw.theory-lookup
  (%autoadmit rw.theory-lookup-aux)
  (%autoadmit rw.theory-lookup)
  (%autoprove rw.theory-lookup-aux-when-not-consp
              (%restrict default rw.theory-lookup-aux (equal x 'x)))
  (%autoprove forcing-rw.typed-rulemapp-of-rw.theory-lookup-aux
              (%autoinduct rw.theory-lookup-aux)
              (%restrict default rw.theory-lookup-aux (equal x 'x)))
  (%autoprove forcing-rw.rule-list-list-atblp-of-range-of-rw.theory-lookup-aux
              (%autoinduct rw.theory-lookup-aux)
              (%restrict default rw.theory-lookup-aux (equal x 'x)))
  (%autoprove forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory-lookup-aux
              (%autoinduct rw.theory-lookup-aux)
              (%restrict default rw.theory-lookup-aux (equal x 'x)))
  (%autoprove rw.theory-lookup-aux-of-rw.theory
              (%restrict default rw.theory-lookup-aux (equal x '(rw.theory name left right rules))))
  (%autoprove forcing-rw.typed-rulemapp-of-rw.theory-lookup
              (%enable default rw.theory-lookup))
  (%autoprove forcing-rw.rule-list-listp-atblp-of-range-of-rw.theory-lookup
              (%enable default rw.theory-lookup))
  (%autoprove forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory-lookup
              (%enable default rw.theory-lookup)))


(defsection rw.extend-typed-rulemap
  (%autoadmit rw.extend-typed-rulemap)
  (%autoprove forcing-rw.typed-rulemapp-of-rw.extend-typed-rulemap
              (%autoinduct rw.extend-typed-rulemap)
              (%restrict default rw.extend-typed-rulemap (equal rulemap 'rulemap)))
  (%autoprove forcing-rw.rule-list-list-atblp-of-range-of-rw.extend-typed-rulemap
              (%autoinduct rw.extend-typed-rulemap)
              (%restrict default rw.extend-typed-rulemap (equal rulemap 'rulemap))
              (%disable default
                        rw.rule-list-atblp-of-subsetp-when-rw.rule-list-atblp
                        rw.rule-atblp-when-memberp-of-rw.rule-list-atblp
                        unusual-consp-rules))
  (%autoprove forcing-rw.rule-list-list-env-okp-of-range-of-rw.extend-typed-rulemap
              (%autoinduct rw.extend-typed-rulemap)
              (%restrict default rw.extend-typed-rulemap (equal rulemap 'rulemap))
              (%disable default
                        rw.rule-list-env-okp-of-subsetp-when-rw.rule-list-env-okp
                        rw.rule-env-okp-when-memberp-of-rw.rule-list-env-okp
                        unusual-consp-rules))
  (%autoprove lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.extend-typed-rulemap
              (%autoinduct rw.extend-typed-rulemap)
              (%restrict default rw.extend-typed-rulemap (equal rulemap 'rulemap))
              (%disable default
                        all-equalp-of-subsetp-when-all-equalp
                        subsetp-of-rw.leading-symbol-lists-when-subsetp
                        unusual-consp-rules
                        type-set-like-rules))
  (%autoprove forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.extend-typed-rulemap
              (%use (%thm lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.extend-typed-rulemap))
              (%restrict default rw.extend-typed-rulemap (equal rulemap 'rulemap))
              (%enable default all-equalp-removal))
  (%autoprove rw.extend-typed-rulemap-of-nil
              (%restrict default rw.extend-typed-rulemap (equal rulemap ''nil))))


(defsection rw.theory-insert
  (%autoadmit rw.theory-insert-aux)
  (%autoadmit rw.theory-insert)
  (%autoprove rw.theory-insert-aux-under-iff
              (%restrict default rw.theory-insert-aux (equal x 'x)))
  (%autoprove lemma-for-forcing-rw.theoryp-of-rw.theory-insert-aux
              (%autoinduct rw.theory-insert-aux)
              (%restrict default rw.theory-insert-aux (equal x 'x)))
  (%autoprove forcing-rw.theoryp-of-rw.theory-insert-aux
              (%use (%thm lemma-for-forcing-rw.theoryp-of-rw.theory-insert-aux)))
  (%autoprove forcing-rw.theory-name-of-rw.theory-insert-aux
              (%use (%thm lemma-for-forcing-rw.theoryp-of-rw.theory-insert-aux)))
  (%autoprove forcing-rw.theory-atblp-of-rw.theory-insert-aux
              (%autoinduct rw.theory-insert-aux)
              (%restrict default rw.theory-insert-aux (equal x 'x)))
  (%autoprove forcing-rw.theory-env-okp-of-rw.theory-insert-aux
              (%autoinduct rw.theory-insert-aux)
              (%restrict default rw.theory-insert-aux (equal x 'x)))
  (%autoprove lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux
              (%autoinduct rw.theory-insert-aux put-goal rule x)
              (%restrict default rw.theory-insert-aux (equal x 'x))
              (%restrict default rw.theory-lookup-aux (equal x 'x)))
  (%autoprove lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux
              (%autoinduct rw.theory-insert-aux)
              (%restrict default rw.theory-insert-aux (equal x 'x))
              (%restrict default rw.theory-lookup-aux (equal x 'x)))
  (%autoprove forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux
              (%use (%instance (%thm lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux)
                               (goal get-goal)))
              (%use (%instance (%thm lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux))))
  (%autoprove forcing-rw.theoryp-of-rw.theory-insert
              (%enable default rw.theory-insert))
  (%autoprove forcing-rw.theory-atblp-of-rw.theory-insert
              (%enable default rw.theory-insert))
  (%autoprove forcing-rw.theory-env-okp-of-rw.theory-insert
              (%enable default rw.theory-insert))
  (%autoprove forcing-rw.theory-lookup-of-rw.theory-insert
              (%enable default rw.theory-insert rw.theory-lookup))
  (%autoprove forcing-subsetp-of-rw.theory-lookup-aux-and-rw.theory-allrules
              (%autoinduct rw.theory-lookup-aux)
              (%restrict default rw.theory-lookup-aux (equal x 'x))
              (%restrict default definition-of-rw.theory-allrules (equal x 'x)))
  (%autoprove forcing-subsetp-of-rw.theory-lookup-and-rw.theory-allrules
              (%enable default rw.theory-lookup)))


(%autoprove forcing-rw.typed-rulemapp-of-remove-all-from-ranges
            (%cdr-induction x))

(%autoprove forcing-rw.rule-list-list-atblp-of-range-of-remove-all-from-ranges
            (%cdr-induction rulemap)
            (%disable default
                      RW.RULE-LIST-ATBLP-OF-SUBSETP-WHEN-RW.RULE-LIST-ATBLP
                      RW.RULE-LIST-ATBLP-WHEN-NOT-CONSP
                      REMOVE-ALL-WHEN-DISJOINT-FROM-ALLP-AND-CONS-LISTP
                      SIMPLE-FLATTEN-WHEN-NOT-CONSP))

(%autoprove forcing-rw.rule-list-env-okp-of-range-of-remove-all-from-ranges
            (%cdr-induction rulemap)
            (%disable default
                      RW.RULE-LIST-ENV-OKP-OF-SUBSETP-WHEN-RW.RULE-LIST-ENV-OKP
                      RW.RULE-LIST-ENV-OKP-WHEN-NOT-CONSP
                      SUBSETP-WHEN-NOT-CONSP
                      SIMPLE-FLATTEN-WHEN-NOT-CONSP))

(%autoprove lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-remove-all-from-ranges
            (%cdr-induction rulemap)
            (%disable default all-equalp-removal)
            (%disable default
                      RW.RULE-LIST-LHSES-WHEN-NOT-CONSP
                      REMOVE-ALL-WHEN-DISJOINT-FROM-ALLP-AND-CONS-LISTP
                      RW.LEADING-SYMBOL-LIST-WHEN-NOT-CONSP
                      SIMPLE-FLATTEN-WHEN-NOT-CONSP
                      type-set-like-rules
                      unusual-subsetp-rules
                      unusual-consp-rules
                      unusual-memberp-rules))

(%autoprove forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-remove-all-from-ranges
            (%enable default all-equalp-removal)
            (%use (%instance (%thm lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-remove-all-from-ranges)
                             (name (rw.leading-symbol (rw.rule->lhs rule))))))


(defsection rw.theory-delete

  (%autoadmit rw.theory-delete-aux)
  (%autoadmit rw.theory-delete)

  (%autoprove rw.theory-delete-aux-when-not-consp
              (%autoinduct rw.theory-delete-aux)
              (%restrict default rw.theory-delete-aux (equal x 'x)))

  (%autoprove lemma-for-forcing-rw.theoryp-of-rw.theory-delete-aux
              (%autoinduct rw.theory-delete-aux)
              (%restrict default rw.theory-delete-aux (equal x 'x)))

  (%autoprove forcing-rw.theoryp-of-rw.theory-delete-aux
              (%use (%thm lemma-for-forcing-rw.theoryp-of-rw.theory-delete-aux)))

  (%autoprove forcing-rw.theory-name-of-rw.theory-delete-aux
              (%use (%thm lemma-for-forcing-rw.theoryp-of-rw.theory-delete-aux)))

  (%autoprove forcing-rw.theory-atblp-of-rw.theory-delete-aux
              (%autoinduct rw.theory-delete-aux)
              (%restrict default rw.theory-delete-aux (equal x 'x)))

  (%autoprove forcing-rw.theory-env-okp-of-rw.theory-delete-aux
              (%autoinduct rw.theory-delete-aux)
              (%restrict default rw.theory-delete-aux (equal x 'x)))

  (%autoprove lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
              (%autoinduct rw.theory-delete-aux put-goal rule x)
              (%restrict default rw.theory-delete-aux (equal x 'x))
              (%restrict default rw.theory-lookup-aux (equal x 'x)))

  (%autoprove lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
              (%autoinduct rw.theory-delete-aux)
              (%restrict default rw.theory-delete-aux (equal x 'x))
              (%restrict default rw.theory-lookup-aux (equal x 'x)))

  (%autoprove forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
              (%enable default
                       lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
                       lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux))

  (%autoprove forcing-rw.theoryp-of-rw.theory-delete
              (%enable default rw.theory-delete))

  (%autoprove forcing-rw.theory-atblp-of-rw.theory-delete
              (%enable default rw.theory-delete))

  (%autoprove forcing-rw.theory-env-okp-of-rw.theory-delete
              (%enable default rw.theory-delete))

  (%autoprove forcing-rw.theory-lookup-of-rw.theory-delete
              (%enable default rw.theory-delete rw.theory-lookup)))



(defsection rw.theory-insert-list
  (%autoadmit rw.theory-insert-list)
  (%autoprove rw.theory-insert-list-when-not-consp
              (%restrict default rw.theory-insert-list (equal rules 'rules)))
  (%autoprove rw.theory-insert-list-of-cons
              (%restrict default rw.theory-insert-list (equal rules '(cons rule rules))))
  (%autoprove forcing-rw.theoryp-of-rw.theory-insert-list
              (%autoinduct rw.theory-insert-list))
  (%autoprove forcing-rw.theory-atblp-of-rw.theory-insert-list
              (%autoinduct rw.theory-insert-list rules theory))
  (%autoprove forcing-rw.theory-env-okp-of-rw.theory-insert-list
              (%autoinduct rw.theory-insert-list rules theory)))



(defsection rw.theory-delete-list
  (%autoadmit rw.theory-delete-list)
  (%autoprove rw.theory-delete-list-when-not-consp
              (%restrict default rw.theory-delete-list (equal rules 'rules)))
  (%autoprove rw.theory-delete-list-of-cons
              (%restrict default rw.theory-delete-list (equal rules '(cons rule rules))))
  (%autoprove forcing-rw.theoryp-of-rw.theory-delete-list
              (%autoinduct rw.theory-delete-list))
  (%autoprove forcing-rw.theory-atblp-of-rw.theory-delete-list
              (%autoinduct rw.theory-delete-list rules theory))
  (%autoprove forcing-rw.theory-env-okp-of-rw.theory-delete-list
              (%autoinduct rw.theory-delete-list rules theory)))



;; (%autoadmit rw.theory-union)

;; (%autoprove forcing-rw.theoryp-of-rw.theory-union
;;             (%enable default rw.theory-union))


;; (%autoadmit rw.theory-difference)

;; (%autoprove forcing-rw.theoryp-of-rw.theory-difference
;;             (%enable default rw.theory-difference))





(%deflist rw.theory-listp (x)
          (rw.theoryp x))

(%deflist rw.theory-list-atblp (x atbl)
          (rw.theory-atblp x atbl))

(%deflist rw.theory-list-env-okp (x thms)
          (rw.theory-env-okp x thms))

(defsection rw.theory-list-allrules
  (%autoadmit rw.fast-theory-list-all-rules)
  (%autoadmit rw.slow-theory-list-all-rules)
  (%autoadmit rw.theory-list-allrules)

  (%autoprove true-listp-of-rw.fast-theory-list-all-rules
              (%autoinduct rw.fast-theory-list-all-rules)
              (%restrict default rw.fast-theory-list-all-rules (equal x 'x)))

  (%autoprove lemma-for-definition-of-rw.theory-list-allrules
              (%autoinduct rw.fast-theory-list-all-rules)
              (%restrict default rw.fast-theory-list-all-rules (equal x 'x))
              (%restrict default rw.slow-theory-list-all-rules (equal x 'x))
              (%forcingp nil))

  (%autoprove definition-of-rw.theory-list-allrules
              (%enable default rw.theory-list-allrules)
              (%restrict default rw.slow-theory-list-all-rules (equal x 'x))
              (%enable default lemma-for-definition-of-rw.theory-list-allrules)
              (%forcingp nil))

  (%autoprove rw.fast-theory-list-all-rules-elim
              (%enable default
                       lemma-for-definition-of-rw.theory-list-allrules
                       rw.theory-list-allrules))

  (%autoprove forcing-true-listp-of-rw.theory-list-allrules
              (%cdr-induction x)
              (%restrict default definition-of-rw.theory-list-allrules (equal x 'x)))

  (%autoprove forcing-rw.rule-listp-of-rw.theory-list-allrules
              (%cdr-induction x)
              (%restrict default definition-of-rw.theory-list-allrules (equal x 'x)))

  (%autoprove forcing-rw.rule-listp-atblp-of-rw.theory-list-allrules
              (%cdr-induction x)
              (%restrict default definition-of-rw.theory-list-allrules (equal x 'x)))

  (%autoprove forcing-rw.rule-listp-env-okp-of-rw.theory-list-allrules
              (%cdr-induction x)
              (%restrict default definition-of-rw.theory-list-allrules (equal x 'x))))


(%defmap :map (rw.theory-mapp x)
         :key (symbolp x)
         :val (rw.theoryp x)
         :key-list (symbol-listp x)
         :val-list (rw.theory-listp x))

(%autoprove rw.theory-mapp-of-clean-update
            (%autoinduct clean-update key val map))

(%autoadmit rw.theory-list-atblp-of-range)

(%autoprove rw.theory-list-atblp-of-range-removal
            (%cdr-induction x)
            (%restrict default rw.theory-list-atblp-of-range (equal x 'x)))


(%autoadmit rw.theory-list-env-okp-of-range)

(%autoprove rw.theory-list-env-okp-of-range-removal
            (%cdr-induction x)
            (%restrict default rw.theory-list-env-okp-of-range (equal x 'x)))



;; (%autoprove rw.rule-list-atblp-of-lookup-when-rw.rule-list-atblp-of-simple-flatten-of-range
;;             (%cdr-induction rulemap)
;;             (%disable default
;;                       RW.RULE-LIST-ATBLP-OF-SUBSETP-WHEN-RW.RULE-LIST-ATBLP
;;                       RW.RULE-LIST-ATBLP-WHEN-NOT-CONSP))

;; (%autoprove rw.rule-list-env-okp-of-lookup-when-rw.rule-list-atblp-of-simple-flatten-of-range
;;             (%cdr-induction rulemap)
;;             (%disable default
;;                       RW.RULE-LIST-ENV-OKP-OF-SUBSETP-WHEN-RW.RULE-LIST-ENV-OKP
;;                       RW.RULE-LIST-ENV-OKP-WHEN-NOT-CONSP))












