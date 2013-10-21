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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(local (in-theory (e/d (booleanp-of-rw.trace->iffp)
                       (forcing-booleanp-of-rw.trace->iffp))))



(defund rw.crewrite-if-specialcase-same-trace (x y z)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (rw.tracep z)
                              (rw.trace->iffp x)
                              (equal (rw.trace->iffp y) (rw.trace->iffp z))
                              (equal (rw.trace->rhs y) (rw.trace->rhs z))
                              (equal (rw.hypbox->left (rw.trace->hypbox y))
                                     (cons (logic.function 'not (list (rw.trace->rhs x)))
                                           (rw.hypbox->left (rw.trace->hypbox x))))
                              (equal (rw.hypbox->left (rw.trace->hypbox z))
                                     (cons (rw.trace->rhs x)
                                           (rw.hypbox->left (rw.trace->hypbox x))))
                              (equal (rw.hypbox->right (rw.trace->hypbox y))
                                     (rw.hypbox->right (rw.trace->hypbox x)))
                              (equal (rw.hypbox->right (rw.trace->hypbox z))
                                     (rw.hypbox->right (rw.trace->hypbox x))))))
  (rw.trace 'crewrite-if-specialcase-same
            (rw.trace->hypbox x)
            (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) (rw.trace->lhs z)))
            (rw.trace->rhs y)
            (rw.trace->iffp y)
            (list x y z)
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-if-specialcase-same-trace)))

 (defthmd lemma-rw.trace->method-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->method (rw.crewrite-if-specialcase-same-trace x y z))
          'crewrite-if-specialcase-same))

 (defthm rw.trace->hypbox-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->hypbox (rw.crewrite-if-specialcase-same-trace x y z))
          (rw.trace->hypbox x)))

 (defthm rw.trace->lhs-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->lhs (rw.crewrite-if-specialcase-same-trace x y z))
          (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) (rw.trace->lhs z)))))

 (defthm rw.trace->rhs-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->rhs (rw.crewrite-if-specialcase-same-trace x y z))
          (rw.trace->rhs y)))

 (defthm forcing-rw.trace->iffp-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->iffp (rw.crewrite-if-specialcase-same-trace x y z))
          (rw.trace->iffp y)))

 (defthmd lemma-rw.trace->subtraces-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->subtraces (rw.crewrite-if-specialcase-same-trace x y z))
          (list x y z)))

 (defthmd lemma-rw.trace->extras-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace->extras (rw.crewrite-if-specialcase-same-trace x y z))
          nil))

 (defthm forcing-rw.tracep-of-rw.crewrite-if-specialcase-same-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)))
            (equal (rw.tracep (rw.crewrite-if-specialcase-same-trace x y z))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.crewrite-if-specialcase-same-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)
                        (rw.trace-atblp z atbl)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.crewrite-if-specialcase-same-trace x y z) atbl)
                   t)))

 (local (in-theory (disable rw.crewrite-if-specialcase-same-trace)))
 (local (in-theory (enable lemma-rw.trace->method-of-rw.crewrite-if-specialcase-same-trace
                           lemma-rw.trace->subtraces-of-rw.crewrite-if-specialcase-same-trace
                           lemma-rw.trace->extras-of-rw.crewrite-if-specialcase-same-trace)))

 (defthmd lemma-forcing-rw.crewrite-if-specialcase-same-tracep-of-rw.crewrite-if-specialcase-same-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)
                        (rw.trace->iffp x)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (equal (rw.trace->rhs y) (rw.trace->rhs z))
                        (equal (rw.hypbox->left (rw.trace->hypbox y))
                               (cons (logic.function 'not (list (rw.trace->rhs x)))
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->left (rw.trace->hypbox z))
                               (cons (rw.trace->rhs x)
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->right (rw.trace->hypbox y))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        (equal (rw.hypbox->right (rw.trace->hypbox z))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        ))
            (equal (rw.crewrite-if-specialcase-same-tracep (rw.crewrite-if-specialcase-same-trace x y z))
                   t))
   :hints(("Goal" :in-theory (enable rw.crewrite-if-specialcase-same-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-specialcase-same-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)
                        (rw.trace->iffp x)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (equal (rw.trace->rhs y) (rw.trace->rhs z))
                        (equal (rw.hypbox->left (rw.trace->hypbox y))
                               (cons (logic.function 'not (list (rw.trace->rhs x)))
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->left (rw.trace->hypbox z))
                               (cons (rw.trace->rhs x)
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->right (rw.trace->hypbox y))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        (equal (rw.hypbox->right (rw.trace->hypbox z))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        ))
            (equal (rw.trace-step-okp (rw.crewrite-if-specialcase-same-trace x y z) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.crewrite-if-specialcase-same-tracep-of-rw.crewrite-if-specialcase-same-trace))))

 (defthm forcing-rw.trace-okp-of-rw.crewrite-if-specialcase-same-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)
                        (rw.trace->iffp x)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (equal (rw.trace->rhs y) (rw.trace->rhs z))
                        (equal (rw.hypbox->left (rw.trace->hypbox y))
                               (cons (logic.function 'not (list (rw.trace->rhs x)))
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->left (rw.trace->hypbox z))
                               (cons (rw.trace->rhs x)
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->right (rw.trace->hypbox y))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        (equal (rw.hypbox->right (rw.trace->hypbox z))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        ;; ---
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)
                        (rw.trace-okp z defs)))
            (equal (rw.trace-okp (rw.crewrite-if-specialcase-same-trace x y z) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.crewrite-if-specialcase-same-trace x y z) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-specialcase-same-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.trace-step-env-okp (rw.crewrite-if-specialcase-same-trace x y z) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.crewrite-if-specialcase-same-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)
                        (rw.trace-env-okp z defs thms atbl)))
            (equal (rw.trace-env-okp (rw.crewrite-if-specialcase-same-trace x y z) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.crewrite-if-specialcase-same-trace x y z) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-specialcase-same-trace))))

 (defthm rw.collect-forced-goals-of-rw.crewrite-if-specialcase-same-trace
   (equal (rw.collect-forced-goals (rw.crewrite-if-specialcase-same-trace x y z))
          (fast-merge (rw.collect-forced-goals x)
                      (fast-merge (rw.collect-forced-goals y)
                                  (rw.collect-forced-goals z))))
   :hints(("Goal" :expand (rw.collect-forced-goals (rw.crewrite-if-specialcase-same-trace x y z))))))




(defund rw.crewrite-if-generalcase-trace (x y z)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (rw.tracep z)
                              (rw.trace->iffp x)
                              (equal (rw.trace->iffp y) (rw.trace->iffp z))
                              (equal (rw.hypbox->left (rw.trace->hypbox y))
                                     (cons (logic.function 'not (list (rw.trace->rhs x)))
                                           (rw.hypbox->left (rw.trace->hypbox x))))
                              (equal (rw.hypbox->left (rw.trace->hypbox z))
                                     (cons (rw.trace->rhs x)
                                           (rw.hypbox->left (rw.trace->hypbox x))))
                              (equal (rw.hypbox->right (rw.trace->hypbox y))
                                     (rw.hypbox->right (rw.trace->hypbox x)))
                              (equal (rw.hypbox->right (rw.trace->hypbox z))
                                     (rw.hypbox->right (rw.trace->hypbox x)))
                              )))
  (let ((hypbox (rw.trace->hypbox x))
        (iffp   (rw.trace->iffp y))
        (lhs    (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) (rw.trace->lhs z))))
        (rhs    (logic.function 'if (list (rw.trace->rhs x) (rw.trace->rhs y) (rw.trace->rhs z)))))
    ;; Another optimization it's too bad we lose.
    ;(if (equal lhs rhs)
    ;    (rw.fail-trace hypbox lhs iffp)
    (rw.trace 'crewrite-if-generalcase hypbox lhs rhs iffp (list x y z) nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-if-generalcase-trace)))

 (defthm rw.trace->method-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->method (rw.crewrite-if-generalcase-trace x y z))
          'crewrite-if-generalcase))

 (defthm rw.trace->hypbox-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->hypbox (rw.crewrite-if-generalcase-trace x y z))
          (rw.trace->hypbox x))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->lhs-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->lhs (rw.crewrite-if-generalcase-trace x y z))
          (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) (rw.trace->lhs z))))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->rhs-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->rhs (rw.crewrite-if-generalcase-trace x y z))
          (logic.function 'if (list (rw.trace->rhs x) (rw.trace->rhs y) (rw.trace->rhs z))))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-rw.trace->iffp-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->iffp (rw.crewrite-if-generalcase-trace x y z))
          (rw.trace->iffp y))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->subtraces-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->subtraces (rw.crewrite-if-generalcase-trace x y z))
          (list x y z))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->extras-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace->extras (rw.crewrite-if-generalcase-trace x y z))
          nil)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-rw.tracep-of-rw.crewrite-if-generalcase-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)))
            (equal (rw.tracep (rw.crewrite-if-generalcase-trace x y z))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.crewrite-if-generalcase-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)
                        (rw.trace-atblp z atbl)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.crewrite-if-generalcase-trace x y z) atbl)
                   t))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (disable rw.crewrite-if-generalcase-trace)))

 (defthmd lemma-forcing-rw.crewrite-if-generalcase-tracep-of-rw.crewrite-if-generalcase-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)
                        (rw.trace->iffp x)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (equal (rw.hypbox->left (rw.trace->hypbox y))
                               (cons (logic.function 'not (list (rw.trace->rhs x)))
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->left (rw.trace->hypbox z))
                               (cons (rw.trace->rhs x)
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->right (rw.trace->hypbox y))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        (equal (rw.hypbox->right (rw.trace->hypbox z))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        ))
            (equal (rw.crewrite-if-generalcase-tracep (rw.crewrite-if-generalcase-trace x y z))
                   t))
   :hints(("Goal" :in-theory (enable rw.crewrite-if-generalcase-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-generalcase-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)
                        (rw.trace->iffp x)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (equal (rw.hypbox->left (rw.trace->hypbox y))
                               (cons (logic.function 'not (list (rw.trace->rhs x)))
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->left (rw.trace->hypbox z))
                               (cons (rw.trace->rhs x)
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->right (rw.trace->hypbox y))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        (equal (rw.hypbox->right (rw.trace->hypbox z))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        ))
            (equal (rw.trace-step-okp (rw.crewrite-if-generalcase-trace x y z) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.crewrite-if-generalcase-tracep-of-rw.crewrite-if-generalcase-trace))))

 (defthm forcing-rw.trace-okp-of-rw.crewrite-if-generalcase-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)
                        (rw.trace->iffp x)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (equal (rw.hypbox->left (rw.trace->hypbox y))
                               (cons (logic.function 'not (list (rw.trace->rhs x)))
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->left (rw.trace->hypbox z))
                               (cons (rw.trace->rhs x)
                                     (rw.hypbox->left (rw.trace->hypbox x))))
                        (equal (rw.hypbox->right (rw.trace->hypbox y))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        (equal (rw.hypbox->right (rw.trace->hypbox z))
                               (rw.hypbox->right (rw.trace->hypbox x)))
                        ;; ---
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)
                        (rw.trace-okp z defs)))
            (equal (rw.trace-okp (rw.crewrite-if-generalcase-trace x y z) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.crewrite-if-generalcase-trace x y z) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-generalcase-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-generalcase-trace
   (equal (rw.trace-step-env-okp (rw.crewrite-if-generalcase-trace x y z) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.crewrite-if-generalcase-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)
                        (rw.trace-env-okp z defs thms atbl)))
            (equal (rw.trace-env-okp (rw.crewrite-if-generalcase-trace x y z) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.crewrite-if-generalcase-trace x y z) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-generalcase-trace))))

 (defthm rw.collect-forced-goals-of-rw.crewrite-if-generalcase-trace
   (equal (rw.collect-forced-goals (rw.crewrite-if-generalcase-trace x y z))
          (fast-merge (rw.collect-forced-goals x)
                      (fast-merge (rw.collect-forced-goals y)
                                  (rw.collect-forced-goals z))))
   :hints(("Goal" :expand (rw.collect-forced-goals (rw.crewrite-if-generalcase-trace x y z))))))





(defund rw.assumptions-trace (assms lhs iffp)
  (declare (xargs :guard (and (rw.assmsp assms)
                              (logic.termp lhs)
                              (booleanp iffp))))
  (let ((eqtrace (rw.try-equiv-database lhs (rw.assms->eqdatabase assms) iffp)))
    (and eqtrace
         (rw.trace 'assumptions
                   (rw.assms->hypbox assms)
                   lhs
                   (rw.eqtrace->lhs eqtrace)
                   iffp
                   nil
                   eqtrace))))

(encapsulate
 ()
 (local (in-theory (enable rw.assumptions-trace)))

 (defthmd lemma-rw.trace->method-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->method (rw.assumptions-trace assms lhs iffp))
                   'assumptions)))

 (defthm rw.trace->assms-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->hypbox (rw.assumptions-trace assms lhs iffp))
                   (rw.assms->hypbox assms))))

 (defthm rw.trace->lhs-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->lhs (rw.assumptions-trace assms lhs iffp))
                   lhs)))

 (defthmd lemma-rw.trace->rhs-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->rhs (rw.assumptions-trace assms lhs iffp))
                   (rw.eqtrace->lhs (rw.try-equiv-database lhs (rw.assms->eqdatabase assms) iffp)))))

 (defthm rw.trace->iffp-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->iffp (rw.assumptions-trace assms lhs iffp))
                   iffp)))

 (defthmd lemma-rw.trace->subtraces-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->subtraces (rw.assumptions-trace assms lhs iffp))
                   nil)))

 (defthmd lemma-rw.trace->extras-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace->extras (rw.assumptions-trace assms lhs iffp))
                   (rw.try-equiv-database lhs (rw.assms->eqdatabase assms) iffp))))

 (defthm forcing-rw.tracep-of-rw.assumptions-trace
   (implies (force (and (logic.termp lhs)
                        (booleanp iffp)
                        (rw.assmsp assms)
                        (rw.assumptions-trace assms lhs iffp)))
            (equal (rw.tracep (rw.assumptions-trace assms lhs iffp))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.assumptions-trace
   (implies (force (and (logic.term-atblp lhs atbl)
                        (rw.assms-atblp assms atbl)
                        (rw.assumptions-trace assms lhs iffp)))
            (equal (rw.trace-atblp (rw.assumptions-trace assms lhs iffp) atbl)
                   t)))

 (defthmd lemma-rw.eqtracep-of-rw.eqtrace->extras-of-rw.assumptions-trace
   (implies (force (and (rw.assumptions-trace assms lhs iffp)
                        (rw.assmsp assms)))
            (equal (rw.eqtracep (rw.trace->extras (rw.assumptions-trace assms lhs iffp)))
                   t)))

 (local (in-theory (disable rw.assumptions-trace)))
 (local (in-theory (enable lemma-rw.trace->method-of-rw.assumptions-trace
                           lemma-rw.trace->rhs-of-rw.assumptions-trace
                           lemma-rw.trace->subtraces-of-rw.assumptions-trace
                           lemma-rw.trace->extras-of-rw.assumptions-trace
                           lemma-rw.eqtracep-of-rw.eqtrace->extras-of-rw.assumptions-trace)))

 (defthmd lemma-forcing-rw.assumptions-tracep-of-rw.assumptions-trace
   (implies (force (and (logic.termp lhs)
                        (booleanp iffp)
                        (rw.assmsp assms)
                        (rw.assumptions-trace assms lhs iffp)))
            (equal (rw.assumptions-tracep (rw.assumptions-trace assms lhs iffp))
                   t))
   :hints(("Goal" :in-theory (enable rw.assumptions-tracep
                                     rw.assumptions-trace))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.assumptions-trace
   (implies (force (and (logic.termp lhs)
                        (booleanp iffp)
                        (rw.assmsp assms)
                        (rw.assumptions-trace assms lhs iffp)))
            (equal (rw.trace-step-okp (rw.assumptions-trace assms lhs iffp) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.assumptions-tracep-of-rw.assumptions-trace))))

 (defthm forcing-rw.trace-okp-of-rw.assumptions-trace
   (implies (force (and (logic.termp lhs)
                        (booleanp iffp)
                        (rw.assmsp assms)
                        (rw.assumptions-trace assms lhs iffp)))
            (equal (rw.trace-okp (rw.assumptions-trace assms lhs iffp) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.assumptions-trace assms lhs iffp) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.assumptions-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace-step-env-okp (rw.assumptions-trace assms lhs iffp) defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.assumptions-trace
   (implies (force (rw.assumptions-trace assms lhs iffp))
            (equal (rw.trace-env-okp (rw.assumptions-trace assms lhs iffp) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.assumptions-trace assms lhs iffp) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.assumptions-trace))))

 (defthm rw.collect-forced-goals-of-rw.assumptions-trace
   (equal (rw.collect-forced-goals (rw.assumptions-trace assms lhs iffp))
          nil)
   :hints(("Goal"
           :cases ((rw.assumptions-trace assms lhs iffp))
           :expand (rw.collect-forced-goals (rw.assumptions-trace assms lhs iffp))
           :in-theory (disable (:executable-counterpart ACL2::force))))))





(defund rw.crewrite-rule-trace (hypbox lhs rule sigma iffp traces)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp lhs)
                              (rw.rulep rule)
                              (logic.sigmap sigma)
                              (booleanp iffp)
                              (rw.trace-listp traces)
                              (or (equal (rw.rule->equiv rule) 'equal)
                                  (and iffp (equal (rw.rule->equiv rule) 'iff)))
                              (not (equal 'fail (logic.patmatch (rw.rule->lhs rule) lhs nil)))
                              (submapp (logic.patmatch (rw.rule->lhs rule) lhs nil) sigma)
                              (all-equalp hypbox (rw.trace-list-hypboxes traces))
                              (all-equalp t (rw.trace-list-iffps traces))
                              (all-equalp ''t (rw.trace-list-rhses traces))
                              (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                                     (rw.trace-list-lhses traces)))))
  (rw.trace 'crewrite-rule
            hypbox
            lhs
            (logic.substitute (rw.rule->rhs rule) sigma)
            iffp
            traces
            (list rule sigma)))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-rule-trace)))

 (defthm rw.crewrite-rule-trace-under-iff
   (iff (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces)
        t))

 (defthmd lemma-rw.trace->method-of-rw.crewrite-rule-trace
   (equal (rw.trace->method (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          'crewrite-rule))

 (defthm rw.trace->hypbox-of-rw.crewrite-rule-trace
   (equal (rw.trace->hypbox (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          hypbox))

 (defthm rw.trace->lhs-of-rw.crewrite-rule-trace
   (equal (rw.trace->lhs (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          lhs))

 (defthm rw.trace->rhs-of-rw.crewrite-rule-trace
   (equal (rw.trace->rhs (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          (logic.substitute (rw.rule->rhs rule) sigma)))

 (defthm forcing-rw.trace->iffp-of-rw.crewrite-rule-trace
   (equal (rw.trace->iffp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          iffp))

 (defthmd lemma-rw.trace->subtraces-of-rw.crewrite-rule-trace
   (equal (rw.trace->subtraces (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          traces))

 (defthmd lemma-rw.trace->extras-of-rw.crewrite-rule-trace
   (equal (rw.trace->extras (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          (list rule sigma)))

 (defthm forcing-rw.tracep-of-rw.crewrite-rule-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp lhs)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (booleanp iffp)
                        (rw.trace-listp traces)))
            (equal (rw.tracep (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.crewrite-rule-trace
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp lhs atbl)
                        (rw.rule-atblp rule atbl)
                        (logic.sigma-atblp sigma atbl)
                        (rw.trace-list-atblp traces atbl)))
            (equal (rw.trace-atblp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) atbl)
                   t)))

 (local (in-theory (disable rw.crewrite-rule-trace)))
 (local (in-theory (enable lemma-rw.trace->method-of-rw.crewrite-rule-trace
                           lemma-rw.trace->subtraces-of-rw.crewrite-rule-trace
                           lemma-rw.trace->extras-of-rw.crewrite-rule-trace)))

 (defthmd lemma-forcing-rw.crewrite-rule-tracep-of-rw.crewrite-rule-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp lhs)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (booleanp iffp)
                        (rw.trace-listp traces)
                        (or (equal (rw.rule->equiv rule) 'equal)
                            (and iffp (equal (rw.rule->equiv rule) 'iff)))
                        (not (equal 'fail (logic.patmatch (rw.rule->lhs rule) lhs nil)))
                        (submapp (logic.patmatch (rw.rule->lhs rule) lhs nil) sigma)
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))
                        (all-equalp t (rw.trace-list-iffps traces))
                        (all-equalp ''t (rw.trace-list-rhses traces))
                        (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                               (rw.trace-list-lhses traces))))
            (equal (rw.crewrite-rule-tracep (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
                   t))
   :hints(("Goal" :in-theory (enable rw.crewrite-rule-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.crewrite-rule-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp lhs)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (booleanp iffp)
                        (rw.trace-listp traces)
                        (or (equal (rw.rule->equiv rule) 'equal)
                            (and iffp (equal (rw.rule->equiv rule) 'iff)))
                        (not (equal 'fail (logic.patmatch (rw.rule->lhs rule) lhs nil)))
                        (submapp (logic.patmatch (rw.rule->lhs rule) lhs nil) sigma)
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))
                        (all-equalp t (rw.trace-list-iffps traces))
                        (all-equalp ''t (rw.trace-list-rhses traces))
                        (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                               (rw.trace-list-lhses traces))))
            (equal (rw.trace-step-okp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.crewrite-rule-tracep-of-rw.crewrite-rule-trace))))

 (defthm forcing-rw.trace-okp-of-rw.crewrite-rule-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp lhs)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (booleanp iffp)
                        (rw.trace-listp traces)
                        (or (equal (rw.rule->equiv rule) 'equal)
                            (and iffp (equal (rw.rule->equiv rule) 'iff)))
                        (not (equal 'fail (logic.patmatch (rw.rule->lhs rule) lhs nil)))
                        (submapp (logic.patmatch (rw.rule->lhs rule) lhs nil) sigma)
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))
                        (all-equalp t (rw.trace-list-iffps traces))
                        (all-equalp ''t (rw.trace-list-rhses traces))
                        (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                               (rw.trace-list-lhses traces))
                        ;; ---
                        (rw.trace-list-okp traces defs)))
            (equal (rw.trace-okp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.crewrite-rule-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-rule-trace
   (implies (force (and (rw.rule-atblp rule atbl)
                        (rw.rule-env-okp rule thms)
                        (logic.sigma-atblp sigma atbl)))
            (equal (rw.trace-step-env-okp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp
                                     rw.crewrite-rule-trace-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.crewrite-rule-trace
   (implies (force (and (rw.rule-atblp rule atbl)
                        (rw.rule-env-okp rule thms)
                        (logic.sigma-atblp sigma atbl)
                        (rw.trace-list-env-okp traces defs thms atbl)))
            (equal (rw.trace-env-okp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-rule-trace))))

 (defthm rw.collect-forced-goals-of-rw.crewrite-rule-trace
   (equal (rw.collect-forced-goals (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
          (rw.collect-forced-goals-list traces))
   :hints(("Goal" :expand (rw.collect-forced-goals (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))))))





(defund rw.force-trace (hypbox lhs)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp lhs))))
  (rw.trace 'force hypbox lhs ''t t nil nil))

(encapsulate
 ()
 (local (in-theory (enable rw.force-trace)))

 (defthm rw.force-trace-under-iff
   (iff (rw.force-trace hypbox lhs)
        t))

 (defthmd lemma-rw.trace->method-of-rw.force-trace
   (equal (rw.trace->method (rw.force-trace hypbox lhs))
          'force))

 (defthm rw.trace->hypbox-of-rw.force-trace
   (equal (rw.trace->hypbox (rw.force-trace hypbox lhs))
          hypbox))

 (defthm rw.trace->lhs-of-rw.force-trace
   (equal (rw.trace->lhs (rw.force-trace hypbox lhs))
          lhs))

 (defthm rw.trace->rhs-of-rw.force-trace
   (equal (rw.trace->rhs (rw.force-trace hypbox lhs))
          ''t))

 (defthm forcing-rw.trace->iffp-of-rw.force-trace
   (equal (rw.trace->iffp (rw.force-trace hypbox lhs))
          t))

 (defthmd lemma-rw.trace->subtraces-of-rw.force-trace
   (equal (rw.trace->subtraces (rw.force-trace hypbox lhs))
          nil))

 (defthmd lemma-rw.trace->extras-of-rw.force-trace
   (equal (rw.trace->extras (rw.force-trace hypbox lhs))
          nil))

 (defthm forcing-rw.tracep-of-rw.force-trace
   (implies (force (and (logic.termp lhs)
                        (rw.hypboxp hypbox)))
            (equal (rw.tracep (rw.force-trace hypbox lhs))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.force-trace
   (implies (force (and (logic.term-atblp lhs atbl)
                        (rw.hypbox-atblp hypbox atbl)))
            (equal (rw.trace-atblp (rw.force-trace hypbox lhs) atbl)
                   t)))

 (local (in-theory (disable rw.force-trace)))
 (local (in-theory (enable lemma-rw.trace->method-of-rw.force-trace
                           lemma-rw.trace->subtraces-of-rw.force-trace
                           lemma-rw.trace->extras-of-rw.force-trace)))

 (defthmd lemma-forcing-rw.force-tracep-of-rw.force-trace
   (implies (force (and (logic.termp lhs)
                        (rw.hypboxp hypbox)))
            (equal (rw.force-tracep (rw.force-trace hypbox lhs))
                   t))
   :hints(("Goal" :in-theory (enable rw.force-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.force-trace
   (implies (force (and (logic.termp lhs)
                        (rw.hypboxp hypbox)))
            (equal (rw.trace-step-okp (rw.force-trace hypbox lhs) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.force-tracep-of-rw.force-trace))))

 (defthm forcing-rw.trace-okp-of-rw.force-trace
   (implies (force (and (logic.termp lhs)
                        (rw.hypboxp hypbox)))
            (equal (rw.trace-okp (rw.force-trace hypbox lhs) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.force-trace hypbox lhs) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.force-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.force-trace
   (equal (rw.trace-step-env-okp (rw.force-trace hypbox lhs) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.force-trace
   (equal (rw.trace-env-okp (rw.force-trace hypbox lhs) defs thms atbl)
          t)
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.force-trace hypbox lhs) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.force-trace))))

 (defthm rw.collect-forced-goals-of-rw.force-trace
   (equal (rw.collect-forced-goals (rw.force-trace hypbox lhs))
          (list (rw.trace-formula (rw.force-trace hypbox lhs))))
   :hints(("Goal" :expand (rw.collect-forced-goals (rw.force-trace hypbox lhs))))))





(defund rw.weakening-trace (hypbox trace)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (rw.tracep trace)
                              (not (rw.hypbox->left (rw.trace->hypbox trace)))
                              (not (rw.hypbox->right (rw.trace->hypbox trace))))))
  (rw.trace 'weakening
            hypbox
            (rw.trace->lhs trace)
            (rw.trace->rhs trace)
            (rw.trace->iffp trace)
            (list trace)
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.weakening-trace)))

 (defthm rw.weakening-trace-under-iff
   (iff (rw.weakening-trace hypbox x)
        t))

 (defthmd lemma-rw.trace->method-of-rw.weakening-trace
   (equal (rw.trace->method (rw.weakening-trace hypbox trace))
          'weakening))

 (defthm rw.trace->hypbox-of-rw.weakening-trace
   (equal (rw.trace->hypbox (rw.weakening-trace hypbox trace))
          hypbox))

 (defthm rw.trace->lhs-of-rw.weakening-trace
   (equal (rw.trace->lhs (rw.weakening-trace hypbox trace))
          (rw.trace->lhs trace)))

 (defthm rw.trace->rhs-of-rw.weakening-trace
   (equal (rw.trace->rhs (rw.weakening-trace hypbox trace))
          (rw.trace->rhs trace)))

 (defthm forcing-rw.trace->iffp-of-rw.weakening-trace
   (equal (rw.trace->iffp (rw.weakening-trace hypbox trace))
          (rw.trace->iffp trace)))

 (defthmd lemma-rw.trace->subtraces-of-rw.weakening-trace
   (equal (rw.trace->subtraces (rw.weakening-trace hypbox trace))
          (list trace)))

 (defthmd lemma-rw.trace->extras-of-rw.weakening-trace
   (equal (rw.trace->extras (rw.weakening-trace hypbox trace))
          nil))

 (defthm forcing-rw.tracep-of-rw.weakening-trace
   (implies (force (and (rw.tracep trace)
                        (rw.hypboxp hypbox)))
            (equal (rw.tracep (rw.weakening-trace hypbox trace))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.weakening-trace
   (implies (force (and (rw.trace-atblp trace atbl)
                        (rw.hypbox-atblp hypbox atbl)))
            (equal (rw.trace-atblp (rw.weakening-trace hypbox trace) atbl)
                   t)))

 (local (in-theory (disable rw.weakening-trace)))
 (local (in-theory (enable lemma-rw.trace->method-of-rw.weakening-trace
                           lemma-rw.trace->subtraces-of-rw.weakening-trace
                           lemma-rw.trace->extras-of-rw.weakening-trace)))

 (defthmd lemma-forcing-rw.weakening-tracep-of-rw.weakening-trace
   (implies (force (and (rw.tracep trace)
                        (rw.hypboxp hypbox)
                        (not (rw.hypbox->left (rw.trace->hypbox trace)))
                        (not (rw.hypbox->right (rw.trace->hypbox trace)))))
            (equal (rw.weakening-tracep (rw.weakening-trace hypbox trace))
                   t))
   :hints(("Goal" :in-theory (enable rw.weakening-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.weakening-trace
   (implies (force (and (rw.tracep trace)
                        (rw.hypboxp hypbox)
                        (not (rw.hypbox->left (rw.trace->hypbox trace)))
                        (not (rw.hypbox->right (rw.trace->hypbox trace)))))
            (equal (rw.trace-step-okp (rw.weakening-trace hypbox trace) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.weakening-tracep-of-rw.weakening-trace))))

 (defthm forcing-rw.trace-okp-of-rw.weakening-trace
   (implies (force (and (rw.tracep trace)
                        (rw.trace-okp trace defs)
                        (rw.hypboxp hypbox)
                        (not (rw.hypbox->left (rw.trace->hypbox trace)))
                        (not (rw.hypbox->right (rw.trace->hypbox trace)))))
            (equal (rw.trace-okp (rw.weakening-trace hypbox trace) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.weakening-trace hypbox trace) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.weakening-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.weakening-trace
   (equal (rw.trace-step-env-okp (rw.weakening-trace hypbox trace) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.weakening-trace
   (equal (rw.trace-env-okp (rw.weakening-trace hypbox trace) defs thms atbl)
          (rw.trace-env-okp trace defs thms atbl))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.weakening-trace hypbox trace) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.weakening-trace))))

 (defthm rw.collect-forced-goals-of-rw.weakening-trace
   (equal (rw.collect-forced-goals (rw.weakening-trace hypbox trace))
          (rw.collect-forced-goals trace))
   :hints(("Goal" :expand (rw.collect-forced-goals (rw.weakening-trace hypbox trace))))))

