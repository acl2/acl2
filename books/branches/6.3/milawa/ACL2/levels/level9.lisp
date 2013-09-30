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
(include-book "level8")
(include-book "../tactics/rewrite-world")
(include-book "../tactics/world-check")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Essay on Theories and the Level 9 Adapter
;;
;; Developing high-level rewriter traces turns out to be somewhat difficult to
;; do in an efficient way.
;;
;; The most straightforward thing to do would be to save the control structure
;; used for the rewrite alongside of each term that was rewritten.  But the
;; control structure includes the entire theory, which is generally quite
;; large.  We really do not want to redundantly repeat a whole huge list of
;; rewrite rules all the time, because then we would have to check them all the
;; time.
;;
;; The adapter for rewrite traces addressed a similar problem with the list of
;; definitions.  But theories are harder, because while the definitions don't
;; change during the course of a proof, we're always adding and removing rules
;; from theories or rewriting with different theories altogether.
;;
;; The first idea I had about addressing this was to introduce dynamic adapters
;; which would allow you to change a theory on the fly as you descended into
;; the proof.  This would require extending skeletons with annotations about
;; the changes being made to theories, and altering %enable and %disable to
;; actually affect skeletons when a skeleton is active.
;;
;; But this suggests a slightly different strategy.  Rather than complicate the
;; level 9 proof checker with dynamically changing theories that it must pass
;; around and handle, why not just preprocess the skeleton, gathering all the
;; theories which will be used ahead of time and then refer back to them by
;; name.  Then, nothing need be changed dynamically.  This approach also works
;; for the noexec list, giving us very tight, simple urewrite traces.
;;
;; Of course, we still need a way to record the changes we've made to the
;; theories we are using and present the level 9 proof checker with the list of
;; theories we will be using.
;;
;; It was at this point that I moved a lot of previously "interface" code into
;; the logic in the form of tactic.worldp, and developed the current system to
;; update worlds using tactics that don't change the goals.  The worlds contain
;; all of the flags and things that we need to generate the control structures
;; being used at any given point.  And the whole collection of worlds can be
;; generated from the initial world and the instructions in the tactics,
;; themselves.  So this seems good, because it allows us to avoid repeating all
;; of the rules over and over for each different world.
;;
;; But unfortunately, it seems hard to reconcile this dynamically changing
;; world with our current high-level traces.  Consider that previously, every
;; time we have installed a high-level builder we have done so by just
;; "redefining" the existing ACL2 function, without making any changes to its
;; interface.  But now we are talking about trying to get at the current list
;; of worlds somehow.  I guess we really don't want to change urewrite or
;; crewrite, but we certainly COULD try to change their tactics around a bit so
;; that different information is recorded.  In particular, we should just
;; record change the way their tactics work.
;;
;; Indeed, at the moment, the tactics don't contain any information about the
;; current world they were developed in.  Rather, they expect that world to be
;; passed in, implicitly.  We could change them pretty easily to take, rather
;; than a world, a list of worlds, which have unique indexes so that the tactic
;; knows which world to use.
;;
;; This seems really good in terms of a multi-level thing.  In the level 9
;; proof checker, we can just record the entire list of worlds used.  But
;; later, we will actually verify our tactic system, and we can stop storing
;; the whole preprocessed list of worlds and just begin compiling them on the
;; fly.


(defund level9.step-okp (x worlds defs axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (tactic.world-listp worlds)
                              (definition-listp defs)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ;; The ccstep-list-bldr is the most significant new step and subsumes compile-trace
     ;; whenever crewrite is being used.  But we also add rw.compile-trace as a new rule,
     ;; since, for example, urewrite builds traces but does not use ccsteps to rewrite the
     ;; clauses.
     ((equal method 'rw.world-urewrite-list-bldr) (rw.world-urewrite-list-bldr-okp x worlds atbl))
     (t
      (level8.step-okp x defs axioms thms atbl)))))

(defobligations level9.step-okp
  (rw.world-urewrite-list-bldr
   level8.step-okp))

(encapsulate
 ()
 (local (in-theory (enable level9.step-okp)))

 (defthm@ soundness-of-level9.step-okp
   (implies (and (level9.step-okp x worlds defs axioms thms atbl)
                 (force (and (logic.appealp x)
                             (tactic.world-listp worlds)
                             (tactic.world-list-atblp worlds atbl)
                             (tactic.world-list-env-okp worlds axioms thms)
                             (logic.formula-list-atblp defs atbl)
                             (definition-listp defs)
                             (subsetp defs axioms)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (@obligations level9.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level9.step-okp-when-level8.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level8.step-okp x defs axioms thms atbl)
            (level9.step-okp x worlds defs axioms thms atbl))
   :hints(("Goal" :in-theory (enable level8.step-okp
                                     level7.step-okp
                                     level6.step-okp
                                     level5.step-okp
                                     level4.step-okp
                                     level3.step-okp
                                     level2.step-okp
                                     logic.appeal-step-okp))))

 (defthm level9.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level9.step-okp x worlds defs axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))


(encapsulate
 ()
 (defund level9.flag-proofp-aux (flag x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (if (equal flag 'proof)
                                   (logic.appealp x)
                                 (and (equal flag 'list)
                                      (logic.appeal-listp x)))
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))
                   :measure (two-nats-measure (rank x) (if (equal flag 'proof) 1 0))))
   (if (equal flag 'proof)
       (and (level9.step-okp x worlds defs axioms thms atbl)
            (level9.flag-proofp-aux 'list (logic.subproofs x) worlds defs axioms thms atbl))
     (if (consp x)
         (and (level9.flag-proofp-aux 'proof (car x) worlds defs axioms thms atbl)
              (level9.flag-proofp-aux 'list (cdr x) worlds defs axioms thms atbl))
       t)))

 (definlined level9.proofp-aux (x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level9.flag-proofp-aux 'proof x worlds defs axioms thms atbl))

 (definlined level9.proof-listp-aux (x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level9.flag-proofp-aux 'list x worlds defs axioms thms atbl))

 (defthmd definition-of-level9.proofp-aux
   (equal (level9.proofp-aux x worlds defs axioms thms atbl)
          (and (level9.step-okp x worlds defs axioms thms atbl)
               (level9.proof-listp-aux (logic.subproofs x) worlds defs axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level9.proofp-aux level9.proof-listp-aux level9.flag-proofp-aux))))

 (defthmd definition-of-level9.proof-listp-aux
   (equal (level9.proof-listp-aux x worlds defs axioms thms atbl)
          (if (consp x)
              (and (level9.proofp-aux (car x) worlds defs axioms thms atbl)
                   (level9.proof-listp-aux (cdr x) worlds defs axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level9.proofp-aux level9.proof-listp-aux level9.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level9.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level9.proof-listp)))))



(defthm level9.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level9.proofp-aux x worlds defs axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level9.proofp-aux))))

(defthm level9.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level9.proof-listp-aux x worlds defs axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level9.proof-listp-aux))))

(defthm level9.proof-listp-aux-of-cons
  (equal (level9.proof-listp-aux (cons a x) worlds defs axioms thms atbl)
         (and (level9.proofp-aux a worlds defs axioms thms atbl)
              (level9.proof-listp-aux x worlds defs axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level9.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level9.proofp-aux
                (equal (booleanp (level9.proofp-aux x worlds defs axioms thms atbl))
                       t))
         (t booleanp-of-level9.proof-listp-aux
            (equal (booleanp (level9.proof-listp-aux x worlds defs axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level9.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level9.proof-listp-aux (x worlds defs axioms thms atbl)
  (level9.proofp-aux x worlds defs axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level9.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level9.step-okp)
                   (mapp atbl)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3)
                   (logic.formula-list-atblp defs atbl)
                   (definition-listp defs)
                   (subsetp defs axioms)
                   (tactic.world-listp worlds)
                   (tactic.world-list-atblp worlds atbl)
                   (tactic.world-list-env-okp worlds axioms thms)
                   )
  :thms ((proof logic.provablep-when-level9.proofp-aux
                (implies (and (logic.appealp x)
                              (level9.proofp-aux x worlds defs axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level9.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level9.proof-listp-aux x worlds defs axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level9.proofp-aux))))


(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level9.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level9.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level9.proofp-aux x worlds defs axioms thms atbl)
                                t)))
         (t level9.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level9.proof-listp-aux x worlds defs axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level9.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level9.proofp-aux-when-logic.proofp
                    level9.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level9.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level9.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level9.proofp-aux (logic.provable-witness formula axioms thms atbl) worlds defs axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level9.proofp-aux-when-logic.proofp))))


;; The level 9 adapter trace will be named level9.proofp and will have, as its extras,
;; a list of the form (defs worlds core).

(defun@ level9.static-checksp (worlds defs axioms thms atbl)
  ;; NOTE!  We leave this enabled!
  (declare (xargs :guard (and (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (mapp atbl)
       (@obligations level9.step-okp)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'if atbl)) 3)
       (definition-listp defs)
       (logic.fast-arities-okp (logic.formula-list-arities defs nil) atbl)
       (ordered-list-subsetp (mergesort defs) (mergesort axioms))
       (tactic.world-listp worlds)
       (tactic.fast-world-list-atblp worlds atbl)
       (tactic.fast-world-list-env-okp worlds axioms thms)))

(defund@ level9.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'level9.proofp)
         (not subproofs)
         (tuplep 3 extras)
         (let ((defs   (first extras))
               (worlds (second extras))
               (core   (third extras)))
           (and
            (ACL2::time$ (level9.static-checksp worlds defs axioms thms atbl))
            (logic.appealp core)
            (equal conclusion (logic.conclusion core))
            (level9.proofp-aux core worlds defs axioms thms atbl))))))

(defthm booleanp-of-level9.proofp
  (equal (booleanp (level9.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level9.proofp))))

(defthm logic.provablep-when-level9.proofp
  (implies (and (logic.appealp x)
                (level9.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (e/d (level9.proofp)
                          (logic.provablep-when-level9.proofp-aux))
          :use ((:instance logic.provablep-when-level9.proofp-aux
                           (x      (third (logic.extras x)))
                           (defs   (first (logic.extras x)))
                           (worlds (second (logic.extras x))))))))

(defun level9.adapter (proof defs initial-world all-worlds)
  (declare (xargs :mode :program)
           (ignore initial-world))
  (logic.appeal 'level9.proofp
                (logic.conclusion proof)
                nil
                (list defs all-worlds proof)))

