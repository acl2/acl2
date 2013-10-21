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
;;       Copyright (C) 2005-2007 by Jared Davis <jared@cs.utexas.edu>        ;;
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
(include-book "crewrite-start")
(local (include-book "crewrite-local-settings"))
(%interactive)


(local (%max-proof-size 0))
(local (%quiet t))

(%autoprove lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core

            (%autoinduct rw.flag-crewrite)
            (%disable default
                      ;; Maybe these cause some problems.
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free)

            (%disable default
                      ;; The theory is already really tight, but there are a few things
                      ;; we're missing, probably because we added the syntax evaluator
                      ;; later on and who knows why for consp-when-consp-of-cdr-cheap.
                      consp-when-consp-of-cdr-cheap
                      forcing-logic.functionp-when-rewrite.syntaxp-base-evaluablep
                      logic.constant-listp-of-logic.function-args-when-rewrite.syntaxp-base-evaluablep)


            ;; Phase 1.  Simplify the resulting induction goals before opening up the
            ;; definitions.

            (%forcingp
             ;; seems like a good idea until goals have settled down
             nil)

            (%liftlimit
             ;; probably not ideal, but this was a good number for fast-image
             10)

            (%splitlimit
             ;; probably not ideal, but this was a good number for fast-image
             2)

            (%betamode
             ;; With betamode nil, the initial waterfall takes 769 seconds and produces 988
             ;; goals.  If we subsequently set betamode=t and enable the splitters and the
             ;; fast-pruning disables, finishing the settling down takes 759 seconds and we
             ;; are left with 806 goals.  So, betamode nil gives a total phase1 time of
             ;; 1528 seconds.
             ;;
             ;; Alternately, we can set betamode t from the beginning.  This increases the
             ;; time of this initial waterfall pass to 1770 seconds, so clearly we want to
             ;; stop beta reduction from happening, initially.
             nil)

            (%waterfall default 400)

            (%betamode t)
            (%enable default
                     splitters
                     special-disables-for-fast-pruning)

            ;; with betamode t, 759 seconds, 806 goals remain
            (%waterfall default 400)


            ;; restrictions as before
            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

            (%disable default ;; speed hint
                      rw.crewrite-try-rules-when-not-consp
                      rw.crewrite-core-list-when-not-consp
                      rw.crewrite-relieve-hyps-when-not-consp
                      rw.crewrite-try-matches-when-not-consp
                      rw.tracep-when-memberp-of-rw.trace-listp
                      minus-when-not-less
                      minus-when-zp-right-cheap
                      minus-when-zp-left-cheap
                      logic.termp-when-not-consp-cheap
                      logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
                      forcing-logic.lambda-actuals-of-logic.substitute
                      forcing-logic.function-args-of-logic.substitute)

;; old size: crewrite-tracep.pcert.out:;; Proof size: 8,560,621,231 conses.
;; new trick: ;; Proof size: 4,254,244,542 conses.
            (%betamode t)
            (%crewrite default)

            (%waterfall default 400)

            (%enable default
                     rw.crewrite-try-rules-when-not-consp
                     rw.tracep-when-memberp-of-rw.trace-listp
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules
                     unusual-consp-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     min
                     logic.termp-when-invalid-maybe-expensive)

            (%disable default
                      squeeze-law-one
                      squeeze-law-two
                      squeeze-law-three
                      minus-when-not-less
                      not-equal-when-less
                      |a <= b, c != 0 --> a < b+c|
                      one-plus-trick
                      |a <= b, c != 0 --> a < c+b|
                      nfix-when-zp-cheap
                      nfix-when-not-natp-cheap
                      zp-when-not-natp-cheap
                      natp-when-zp-cheap
                      |a <= b, b <= c --> a < 1+c|
                      equal-of-booleans-rewrite
                      gather-constants-from-less-of-plus
                      gather-constants-from-less-of-plus-two
                      minus-when-zp-left-cheap
                      minus-when-zp-right-cheap
                      plus-when-zp-left-cheap
                      plus-when-zp-right-cheap
                      gather-constants-from-equal-of-plus
                      equal-of-non-symbol-and-symbol-cheap
                      equal-of-non-cons-and-cons-cheap
                      equal-of-cons-and-non-cons-cheap
                      equal-of-non-nat-and-nat-cheap
                      equal-of-nat-and-non-nat-cheap
                      equal-of-symbol-and-non-symbol-cheap)

            (%waterfall default 400) ;; 169 seconds, 20 goals remain
            (%car-cdr-elim)
            (%auto))



;; Some code for debugging proof times:

;; (acl2::defttag my-check)
;;
;; (defun report-times ()
;;   (declare (xargs :guard t))
;;   (acl2::cw "Report times not redefined.~%"))
;;
;; (acl2::progn!
;;
;;  (acl2::set-raw-mode t)
;;
;;  (acl2::defparameter *step-times-ht* (acl2::make-hash-table :test #'acl2::eq :size 1024))
;;
;;  (acl2::defun level9.flag-proofp-aux (flag x worlds defs axioms thms atbl)
;;               (if (equal flag 'proof)
;;                   (let* ((start-time (ACL2::get-internal-real-time))
;;                          (step1-okp  (level9.step-okp x worlds defs axioms thms atbl))
;;                          (end-time   (ACL2::get-internal-real-time))
;;                          (old-time   (or (ACL2::gethash (logic.method x) *step-times-ht*) 0)))
;;                     (ACL2::progn
;;                      (acl2::setf (acl2::gethash (logic.method x) *step-times-ht*)
;;                                  (acl2::+ old-time (acl2::- end-time start-time)))
;;                      (and step1-okp
;;                           (level9.flag-proofp-aux 'list (logic.subproofs x) worlds defs axioms thms atbl))))
;;                 (if (consp x)
;;                     (and (level9.flag-proofp-aux 'proof (car x) worlds defs axioms thms atbl)
;;                          (level9.flag-proofp-aux 'list (cdr x) worlds defs axioms thms atbl))
;;                   t)))
;;
;;  (acl2::defun report-times ()
;;               (acl2::maphash (lambda (key val)
;;                                (acl2::format t "~a: ~a seconds.~%"
;;                                              key
;;                                              (acl2::/ (acl2::coerce val 'acl2::float) acl2::internal-time-units-per-second)))
;;                              *step-times-ht* )))





(%autoprove forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.trace-listp-of-rw.cresult->data-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.trace-listp-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove forcing-rw.cachep-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))





#||

;; A previous, working attempt.

(%autoprove lemma-for-forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core

            (%autoinduct rw.flag-crewrite)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free)

            ;; Interlaced splitting and lightweight rewriting to control case explosion

            (%quiet t)
            (%betamode nil)
            (%forcingp nil)
            (%crewrite default)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 3 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 0 :splitlimit 0)
            (%quiet nil)

            (%enable default
                     splitters
                     special-disables-for-fast-pruning)
            (%betamode once)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 0 :splitlimit 0)

            (%crewrite default)
            (%cleanup)

            ;; This might look a little scary, but observe that no single goal is affected
            ;; by more than one of these expansions.

            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

            (%disable default ;; speed hint
                      rw.crewrite-try-rules-when-not-consp
                      rw.tracep-when-memberp-of-rw.trace-listp)

            (%crewrite default)

            (%auto :strategy (split cleanup crewrite))

            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition
                     rw.crewrite-try-rules-when-not-consp
                     rw.tracep-when-memberp-of-rw.trace-listp
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules
                     unusual-consp-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     min)

            (%auto :strategy (split cleanup urewrite crewrite elim)))


||#