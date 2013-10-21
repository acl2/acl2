;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "core")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Implementing Magic Evaluation
;;
;; Now that we can inspect the global function definitions and arity table, we can
;; make the magic-evaluator executable for the current definitions.

(encapsulate
 ()
 (ACL2::defttag executable-magic-evaluator)
 (ACL2::progn!
  (ACL2::set-raw-mode t)

  (ACL2::defun magic-evaluator (x defs)
               (cond ((not (logic.termp x))
                      (ACL2::er hard 'magic-evaluator "Tried to evaluate a non-term, ~x0.~%" x))
                     ((not (logic.groundp x))
                      (ACL2::er hard 'magic-evaluator "Tried to evaluate a non-ground term, ~x0.~%" x))
                     ((ACL2::eq defs (tactic.harness->defs (ACL2::w ACL2::*the-live-state*)))
                      (if (logic.warn-term-atblp x (tactic.harness->atbl (ACL2::w ACL2::*the-live-state*)))
                          (list 'quote (ACL2::eval x))
                        (ACL2::er hard 'magic-evaluator "Tried to evaluate a term with improper arity, ~x0.~%" x)))
                     ;((ACL2::eq defs (tactic.harness->syndefs (ACL2::w ACL2::*the-live-state*)))
                     ; ;; BOZO we should check the atbl with respect to the syndefs.  We don't even have an
                     ; ;; atbl set up for this.  But we could add one and just update it in %syntax-defun-fn.
                     ; (list 'quote (ACL2::eval x)))
                     (t
                      (ACL2::er hard 'magic-evaluator "Tried to evaluate with the wrong definitions.  ~
                                                      Only (tactic.harness->defs (ACL2::w ACL2::state)) or ~
                                                      (tactic.harness->syndefs (ACL2::w ACL2::state)) are ~
                                                      permitted.~%"))))


  ;; We were able to redefine the magic-evaluator above because we already had
  ;; ACL2::eval available to us.  But ACL2 has no built-in function for creating
  ;; a Milawa proof corresponding to an execution.  But we can easily introduce
  ;; one, by modifying the generic-evaluator-bldr to not take a clock.

  (ACL2::defun ACL2::eval-bldr (flag x defs)
               (if (equal flag 'term)
                   (cond ((logic.constantp x)
                          (build.reflexivity x))
                         ((logic.variablep x)
                          nil)
                         ((logic.functionp x)
                          (let ((fn   (logic.function-name x))
                                (args (logic.function-args x)))
                            (if (and (equal fn 'if)
                                     (equal (len args) 3))
                                (let ((arg1-proof (ACL2::eval-bldr 'term (first args) defs)))
                                  (and arg1-proof
                                       (let ((arg1-prime (logic.=rhs (logic.conclusion arg1-proof))))
                                         (if (logic.unquote arg1-prime)
                                             (let ((arg2-proof (ACL2::eval-bldr 'term (second args) defs)))
                                               (and arg2-proof
                                                    (eval-lemma-1-bldr arg1-proof arg2-proof (third args))))
                                           (let ((arg3-proof (ACL2::eval-bldr 'term (third args) defs)))
                                             (and arg3-proof
                                                  (eval-lemma-2-bldr arg1-proof arg3-proof (second args))))))))
                              (let ((aproofs+ (ACL2::eval-bldr 'list args defs)))
                                (and aproofs+
                                     (let* ((aproofs (cdr aproofs+))
                                            (vals    (logic.=rhses (logic.strip-conclusions aproofs))))
                                       (if (memberp fn (domain (logic.initial-arity-table)))
                                           (and (equal (cdr (lookup fn (logic.initial-arity-table))) (len aproofs))
                                                (build.transitivity-of-pequal (build.pequal-by-args fn aproofs)
                                                                              (build.base-eval (logic.function fn vals))))
                                         (let* ((def (definition-list-lookup fn defs)))
                                           (and def
                                                (let ((formals (logic.function-args (logic.=lhs def)))
                                                      (body    (logic.=rhs def)))
                                                  (and (equal (len formals) (len aproofs))
                                                       (let* ((sigma       (pair-lists formals vals))
                                                              (ground-body (logic.substitute body sigma))
                                                              (body-proof  (ACL2::eval-bldr 'term ground-body defs)))
                                                         (and body-proof
                                                              (build.transitivity-of-pequal (build.pequal-by-args fn aproofs)
                                                                                            (build.transitivity-of-pequal
                                                                                             (build.instantiation (build.axiom def) sigma)
                                                                                             body-proof)))))))))))))))
                         ((logic.lambdap x)
                          (let ((formals  (logic.lambda-formals x))
                                (body     (logic.lambda-body x))
                                (actuals  (logic.lambda-actuals x)))
                            (let ((aproofs+ (ACL2::eval-bldr 'list actuals defs)))
                              (and aproofs+
                                   (let* ((vals       (logic.=rhses (logic.strip-conclusions (cdr aproofs+))))
                                          (sigma      (pair-lists formals vals))
                                          (body-proof (ACL2::eval-bldr 'term (logic.substitute body sigma) defs)))
                                     (and body-proof
                                          (build.transitivity-of-pequal (build.transitivity-of-pequal
                                                                         (build.lambda-pequal-by-args formals body (cdr aproofs+))
                                                                         (build.beta-reduction formals body vals))
                                                                        body-proof)))))))
                         (t nil))
                 (if (consp x)
                     (let ((first (ACL2::eval-bldr 'term (car x) defs))
                           (rest  (ACL2::eval-bldr 'list (cdr x) defs)))
                       (if (and first rest)
                           (cons t (cons first (cdr rest)))
                         nil))
                   (cons t nil))))

  (ACL2::defun magic-evaluator-bldr (x defs)
               (cond ((not (logic.termp x))
                      (ACL2::er hard 'magic-evaluator-bldr "Tried to evaluate-bldr a non-term, ~x0.~%" x))
                     ((not (logic.groundp x))
                      (ACL2::er hard 'magic-evaluator-bldr "Tried to evaluate-bldr a non-ground term, ~x0.~%" x))
                     ((not (logic.warn-term-atblp x (tactic.harness->atbl (ACL2::w ACL2::*the-live-state*))))
                      (ACL2::er hard 'magic-evaluator-bldr "Tried to evaluate-bldr a term with improper arity, ~x0.~%" x))
                     (t
                      (if (ACL2::eq defs (tactic.harness->defs (ACL2::w ACL2::*the-live-state*)))
                          (ACL2::eval-bldr 'term x defs)
                        (ACL2::er hard 'magic-evaluator-bldr "Tried to evaluate-bldr with the wrong definitions. ~
                                                              Only (tactic.harness->defs (ACL2::w ACL2::state)) ~
                                                              are permitted.~%~
                                                              Lengths: ~x0 (should be ~x1)~%~
                                                              Missing: ~x2 ~%~
                                                              Additional: ~x3 ~%~
                                                              Defs are equal (but not eq)?: ~x4~%"
                                  (len defs)
                                  (len (tactic.harness->defs (ACL2::w ACL2::*the-live-state*)))
                                  (fast-difference$ (tactic.harness->defs (ACL2::w ACL2::*the-live-state*)) defs nil)
                                  (fast-difference$ defs (tactic.harness->defs (ACL2::w ACL2::*the-live-state*)) nil)
                                  (equal defs (tactic.harness->defs (ACL2::w ACL2::*the-live-state*))))))))))
