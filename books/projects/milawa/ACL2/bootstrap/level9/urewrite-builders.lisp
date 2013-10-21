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
(include-book "basic-builders") ;; for fail-trace
(%interactive)


(local (%enable default booleanp-of-rw.trace->iffp))
(local (%disable default forcing-booleanp-of-rw.trace->iffp))



(defsection rw.urewrite-if-specialcase-same-trace

  (%autoadmit rw.urewrite-if-specialcase-same-trace)

  (local (%enable default rw.urewrite-if-specialcase-same-trace))

  (%autoprove rw.trace->method-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->hypbox-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->lhs-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->rhs-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->iffp-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->subtraces-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->extras-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove forcing-rw.tracep-of-rw.urewrite-if-specialcase-same-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.urewrite-if-specialcase-same-trace)

  (local (%disable default rw.urewrite-if-specialcase-same-trace))

  (%autoprove lemma-forcing-rw.urewrite-if-specialcase-same-tracep-of-rw.urewrite-if-specialcase-same-trace
              (%enable default rw.urewrite-if-specialcase-same-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-specialcase-same-trace
              (%enable default
                       lemma-forcing-rw.urewrite-if-specialcase-same-tracep-of-rw.urewrite-if-specialcase-same-trace
                       rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.urewrite-if-specialcase-same-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.urewrite-if-specialcase-same-trace x y a)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-specialcase-same-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-specialcase-same-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.urewrite-if-specialcase-same-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.urewrite-if-specialcase-same-trace x y a)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-specialcase-same-trace))

  (%autoprove rw.collect-forced-goals-of-rw.urewrite-if-specialcase-same-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.urewrite-if-generalcase-trace

  (%autoadmit rw.urewrite-if-generalcase-trace)

  (local (%enable default rw.urewrite-if-generalcase-trace))
  (local (%splitlimit 10))

  (%autoprove rw.trace->method-of-rw.urewrite-if-generalcase-trace)
  (%autoprove rw.trace->hypbox-of-rw.urewrite-if-generalcase-trace)
  (%autoprove rw.trace->lhs-of-rw.urewrite-if-generalcase-trace)
  (%autoprove rw.trace->rhs-of-rw.urewrite-if-generalcase-trace)
  (%autoprove rw.trace->iffp-of-rw.urewrite-if-generalcase-trace)
  (%autoprove rw.trace->subtraces-of-rw.urewrite-if-generalcase-trace)
  (%autoprove rw.trace->extras-of-rw.urewrite-if-generalcase-trace)
  (%autoprove forcing-rw.tracep-of-rw.urewrite-if-generalcase-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.urewrite-if-generalcase-trace)

  (local (%disable default rw.urewrite-if-generalcase-trace))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-generalcase-trace
              (%enable default rw.trace-step-okp rw.urewrite-if-generalcase-tracep))

  (%autoprove forcing-rw.trace-okp-of-rw.urewrite-if-generalcase-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.urewrite-if-generalcase-trace x y z)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-generalcase-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-generalcase-trace
              (%enable default rw.trace-step-env-okp rw.urewrite-if-generalcase-tracep))

  (%autoprove forcing-rw.trace-env-okp-of-rw.urewrite-if-generalcase-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.urewrite-if-generalcase-trace x y z)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-generalcase-trace))

  (%autoprove rw.collect-forced-goals-of-rw.urewrite-if-generalcase-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.try-urewrite-rule

  (%autoadmit rw.try-urewrite-rule)

  (local (%enable default rw.try-urewrite-rule))
  (local (%splitlimit 10))

  (%autoprove lemma-forcing-rw.trace->method-of-rw.try-urewrite-rule)
  (%autoprove forcing-rw.trace->hypbox-of-rw.try-urewrite-rule)
  (%autoprove forcing-rw.trace->lhs-of-rw.try-urewrite-rule)
  (%autoprove forcing-rw.trace->iffp-of-rw.try-urewrite-rule)
  (%autoprove lemma-forcing-rw.trace->subtraces-of-rw.try-urewrite-rule)
  (%autoprove lemma-forcing-rw.trace->extras-of-rw.try-urewrite-rule)
  (%autoprove forcing-rw.tracep-of-rw.try-urewrite-rule)
  (%autoprove forcing-rw.trace-atblp-of-rw.try-urewrite-rule)

  (%autoprove lemma-forcing-rw.urewrite-rule-tracep-of-rw.try-urewrite-rule
              (%enable default rw.urewrite-rule-tracep))

  (local (%disable default rw.try-urewrite-rule))
  (local (%enable default
                  lemma-forcing-rw.trace->method-of-rw.try-urewrite-rule
                  lemma-forcing-rw.trace->subtraces-of-rw.try-urewrite-rule
                  lemma-forcing-rw.trace->extras-of-rw.try-urewrite-rule
                  lemma-forcing-rw.urewrite-rule-tracep-of-rw.try-urewrite-rule))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.try-urewrite-rule
              (%enable default rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.try-urewrite-rule
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.try-urewrite-rule hypbox term rule iffp control)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.try-urewrite-rule))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.try-urewrite-rule
              (%enable default rw.trace-step-env-okp rw.urewrite-rule-trace-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.try-urewrite-rule
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.try-urewrite-rule hypbox term rule iffp control)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.try-urewrite-rule))

  (%autoprove forcing-rw.collect-forced-goals-of-rw.try-urewrite-rule
              (%enable default definition-of-rw.collect-forced-goals)))




(defsection rw.try-urewrite-rule-list
  (%autoadmit rw.try-urewrite-rule-list)
  (local (%restrict default rw.try-urewrite-rule-list (equal rules 'rules)))
  (%autoprove forcing-rw.trace->lhs-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.trace->iffp-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.trace->hypbox-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.tracep-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.trace-atblp-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.trace-okp-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.trace-env-okp-of-rw.try-urewrite-rule-list
              (%cdr-induction rules))
  (%autoprove forcing-rw.collect-forced-goals-of-rw.try-urewrite-rule-list
              (%cdr-induction rules)))


(defsection rw.try-urewrite-rules
  (%autoadmit rw.try-urewrite-rules)
  (local (%enable default rw.try-urewrite-rules))
  (%autoprove forcing-rw.trace->lhs-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.trace->iffp-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.trace->hypbox-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.tracep-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.trace-atblp-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.trace-okp-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.trace-env-okp-of-rw.try-urewrite-rules)
  (%autoprove forcing-rw.collect-forced-goals-of-rw.try-urewrite-rules))


(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/urewrite-builders")