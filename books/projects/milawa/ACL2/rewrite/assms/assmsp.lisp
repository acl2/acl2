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
(include-book "hypboxp")
(include-book "add-equality")
(include-book "assmctrl")
(include-book "../../clauses/smart-negate")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Introduction to assumptions.
;;
;; Assumptions allow our conditional rewriter to make more progress by knowing
;; that certain things are true.
;;
;; Where do assumptions come from?  Normally we are rewriting a term which
;; occurs in a clause.  Say the clause is T1 v ... v Tn, and we are rewriting
;; T1.  Then we can think of the clause as an implication:
;;
;;    [| ~T2 ; ... ; ~Tn |] ==> T1
;;
;; We can thus assume ~T2, ..., and ~Tn while rewriting T1.  We call these
;; assumptions CLAUSE ASSUMPTIONS since they come from the clause.  This is one
;; of the reasons clause splitting is so great: splitting up complex literals
;; into lots of simple literals gives us more assumptions to work with.
;;
;; Another source of assumptions is from unsplit literals.  As we are
;; descending through T1, we might encounter (if x y z).  Then, when we rewrite
;; y we can additionally assume x is true, and when we rewrite z we can assume
;; x is false.  We call these CASE ASSUMPTIONS since they come from cases
;; within the term we're rewriting.  Note that case assumptions can occur even
;; if we fully split the clause before rewriting, since ifs can occur in the
;; replacement term in a rewrite rule or in a hypothesis.
;;
;; Unlike ACL2, we don't make assumptions when we backchain.  This may cause us
;; to miss some things, but, along with some other design decisions, it
;; entirely prevents tail biting even without our having to track the literals
;; which lead to our assumptions.
;;
;;
;;
;; Assumption structures and hypboxes.
;;
;; Before we begin rewriting a term, we assume all the other literals in the
;; clause are false and build an "assms" structure for these assumptions.  Each
;; assms structure has three key pieces:
;;
;;   - A "hypbox" where we put the actual terms we have assumed false,
;;   - Additional databases of "inferred" information, and
;;   - A list of terms we believe are true (which are used heuristically
;;     by the rewriter)
;;
;; For obscure efficiency reasons (see crewrite-clause.lisp for details) each
;; hypbox has two "sides", called left and right.  Each side is just a list of
;; terms which we are assuming false, and together the union of left and right
;; gives us all of the terms which have been assumed false.
;;
;; The additional databases are used to "strengthen" our assumptions before we
;; begin rewriting with them.  The idea is that we may want to infer additional
;; information from our assumptions, e.g., if we have assumed a = b and b = c,
;; then we would like to infer a = c.  We keep these databases separate from
;; our hypbox, so that new things may be inferred while leaving predicatable
;; the set of things we have assumed.
;;
;; New assumptions are added to the assumptiosn structure using the following
;; functions:
;;
;;    (rw.assume-left  nhyp assms) ==> assms'
;;    (rw.assume-right nhyp assms) ==> assms'
;;
;; Each of these assumes nhyp is false.  So, if you want to assume that "hyp"
;; is true, you need to assume its negation is false.  The assumption is put
;; into the left or right side of the hypbox as appropriate.  Note that adding
;; new assumptions might contradict previous assumptions, and we discuss this
;; in detail below.
;;
;; Once the database has been created, we can use it to simplify terms with the
;; following function:
;;
;;    (rw.try-assms term iffp assms) ==> eqtrace or nil
;;
;; Nil is returned on failure, and an "eqtrace" is returned when we can
;; simplify term in some way under the given iffp context.  These traces are
;; similar to rewriter traces in that they can be compiled into an actual proof
;; of their conclusion---see eqtracep.lisp for more details.  When an eqtrace
;; is returned, the compiled proof will conclude:
;;
;;    hypbox-formula v (equiv term term') = t
;;
;; Where the hypbox-formula is either:
;;
;;    (clause.clause-formula nhyps-left) v (clause.clause-formula nhyps-right)
;;
;; Or is just the appropriate part of this if the other part is empty.  If both
;; the left and right sides of the hypbox are empty, then rw.try-assums always
;; fails, i.e., returns nil.
;;
;;
;;
;; Dealing with contradictions.
;;
;; Before we rewrite a term, we make clause assumptions for the other literals
;; in the clause.  This might produce a contradiction.  If so, we don't need to
;; do rewriting at all, because it means some Ti and Tj cannot both be false at
;; the same time, so the clause must be true.
;;
;; But we could also encounter a contradiction while making a case assumption.
;; For example, perhaps we are rewriting (if x y z) and we want to assume x is
;; true before rewriting y.  Here, assuming x is true might lead us to discover
;; a contradiction.  Then x must be false, so you might think we should rewrite
;; the whole term (if x y z) to z.
;;
;; But this is so messy that I consider it to be degenerate.  Before we go to
;; rewrite y or z, we should have tried to rewrite x.  If assuming x is true
;; causes a contradiction, then it's my opinion that x should have just been
;; rewritten to nil in the first place.  It might be interesting to try to
;; formalize this idea later, but I haven't tried to do this yet.
;;
;; We can check for a contradiction using the function:
;;
;;   (rw.assms->contradiction assms) ==> nil or proof
;;
;; Nil is returned when there is no contradiction, and otherwise a proof of the
;; hypbox-formula is returned.  If we have an assms structure which already has
;; a contradiction, the contradiction will of course be preserved as we add
;; more assumptions to it.  Hence, during the initial assms setup we can just
;; dump in all the literals from the clause, and check at the end if any
;; contradiction has occurred.


(defsection rw.assmsp

  (defund rw.assmsp (x)
    (declare (xargs :guard t))
    ;; We'd like to use defaggregate but the "implies" is pretty complicated.
    ;; Instead, we use a custom cons structure.
    ;;  (hypbox . contradiction) . ((eqdatabase . trueterms) . ctrl)
    (and (consp (car x)) ;; apparently we care about the consp-ness later on
         (consp (cdr x)) ;; for forcing-equal-of-rw.assms-one
         (consp (car (cdr x)))
         (let ((hypbox        (car (car x)))
               (contradiction (cdr (car x)))
               (eqdatabase    (car (car (cdr x))))
               (trueterms     (cdr (car (cdr x))))
               (ctrl          (cdr (cdr x))))
           (and (rw.hypboxp hypbox)
                (rw.eqdatabasep eqdatabase)
                (rw.eqdatabase-okp eqdatabase hypbox)
                (or (not contradiction)
                    (and (rw.eqtracep contradiction)
                         (rw.eqtrace-contradictionp contradiction)
                         (rw.eqtrace-okp contradiction hypbox)))
                (logic.term-listp trueterms)
                (rw.assmctrlp ctrl)))))

  (definlined rw.assms (hypbox contradiction eqdatabase trueterms ctrl)
    (declare (xargs :guard (and (rw.hypboxp hypbox)
                                (rw.eqdatabasep eqdatabase)
                                (rw.eqdatabase-okp eqdatabase hypbox)
                                (or (not contradiction)
                                    (and (rw.eqtracep contradiction)
                                         (rw.eqtrace-contradictionp contradiction)
                                         (rw.eqtrace-okp contradiction hypbox)))
                                (logic.term-listp trueterms)
                                (rw.assmctrlp ctrl))))
    (cons (cons hypbox contradiction)
          (cons (cons eqdatabase trueterms)
                ctrl)))

  (definlined rw.assms->hypbox (x)
    (declare (xargs :guard (rw.assmsp x)))
    (car (car x)))

  (definlined rw.assms->contradiction (x)
    (declare (xargs :guard (rw.assmsp x)))
    (cdr (car x)))

  (definlined rw.assms->eqdatabase (x)
    (declare (xargs :guard (rw.assmsp x)))
    (car (car (cdr x))))

  (definlined rw.assms->trueterms (x)
    (declare (xargs :guard (rw.assmsp x)))
    (cdr (car (cdr x))))

  (definlined rw.assms->ctrl (x)
    (declare (xargs :guard (rw.assmsp x)))
    (cdr (cdr x)))


  (definlined rw.assms-atblp (x atbl)
    (declare (xargs :guard (and (rw.assmsp x)
                                (logic.arity-tablep atbl))
                    :guard-hints (("Goal" :in-theory (enable rw.assmsp
                                                             rw.assms->hypbox
                                                             rw.assms->eqdatabase
                                                             rw.assms->contradiction
                                                             rw.assms->trueterms)))))
    (let ((hypbox        (rw.assms->hypbox x))
          (eqdatabase    (rw.assms->eqdatabase x))
          (contradiction (rw.assms->contradiction x))
          (trueterms     (rw.assms->trueterms x)))
      (and (rw.hypbox-atblp hypbox atbl)
           (rw.eqdatabase-atblp eqdatabase atbl)
           (or (not contradiction)
               (rw.eqtrace-atblp contradiction atbl))
           (logic.term-list-atblp trueterms atbl))))

  (local (in-theory (enable rw.assmsp
                            rw.assms
                            rw.assms->hypbox
                            rw.assms->contradiction
                            rw.assms->eqdatabase
                            rw.assms->trueterms
                            rw.assms->ctrl
                            rw.assms-atblp)))

  (defthm booleanp-of-rw.assmsp
    (equal (booleanp (rw.assmsp x))
           t))

  (defthm booleanp-of-rw.assms-atblp
    (equal (booleanp (rw.assms-atblp x atbl))
           t))

  (defthm forcing-rw.assmsp-of-rw.assms
    (implies (force (and (rw.hypboxp hypbox)
                         (rw.eqdatabasep eqdatabase)
                         (rw.eqdatabase-okp eqdatabase hypbox)
                         (or (not contradiction)
                             (and (rw.eqtracep contradiction)
                                  (rw.eqtrace-contradictionp contradiction)
                                  (rw.eqtrace-okp contradiction hypbox)))
                         (logic.term-listp trueterms)
                         (rw.assmctrlp ctrl)))
             (equal (rw.assmsp (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
                    t)))

  (defthm forcing-rw.assms-atblp-of-rw.assms
    (implies (force (and (rw.hypbox-atblp hypbox atbl)
                         (rw.eqdatabase-atblp eqdatabase atbl)
                         (or (not contradiction)
                             (rw.eqtrace-atblp contradiction atbl))
                         (logic.term-list-atblp trueterms atbl)))
             (equal (rw.assms-atblp (rw.assms hypbox contradiction eqdatabase trueterms ctrl) atbl)
                    t)))

  (defthm rw.assms->hypbox-of-rw.assms
    (equal (rw.assms->hypbox (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
           hypbox))

  (defthm rw.assms->contradiction-of-rw.assms
    (equal (rw.assms->contradiction (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
           contradiction))

  (defthm rw.assms->eqdatabase-of-rw.assms
    (equal (rw.assms->eqdatabase (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
           eqdatabase))

  (defthm rw.assms->trueterms-of-rw.assms
    (equal (rw.assms->trueterms (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
           trueterms))

  (defthm rw.assms->ctrl-of-rw.assms
    (equal (rw.assms->ctrl (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
           ctrl))

  (defthm forcing-rw.hypboxp-of-rw.assms->hypbox
    (implies (force (rw.assmsp x))
             (equal (rw.hypboxp (rw.assms->hypbox x))
                    t)))

  (defthm forcing-rw.hypbox-atblp-of-rw.assms->hypbox
    (implies (force (rw.assms-atblp x atbl))
             (equal (rw.hypbox-atblp (rw.assms->hypbox x) atbl)
                    t)))

  (defthm forcing-rw.eqdatabasep-of-rw.assms->eqdatabase
    (implies (force (rw.assmsp x))
             (equal (rw.eqdatabasep (rw.assms->eqdatabase x))
                    t)))

  (defthm forcing-rw.eqdatabase-okp-of-rw.assms->eqdatabase
    (implies (force (rw.assmsp x))
             (equal (rw.eqdatabase-okp (rw.assms->eqdatabase x)
                                       (rw.assms->hypbox x))
                    t)))

  (defthm forcing-rw.eqdatabase-atblp-of-rw.assms->eqdatabase
    (implies (force (rw.assms-atblp x atbl))
             (equal (rw.eqdatabase-atblp (rw.assms->eqdatabase x) atbl)
                    t)))

  (defthm rw.assms->contradiction-when-no-assumptions
    (implies (and (not (rw.hypbox->left (rw.assms->hypbox x)))
                  (not (rw.hypbox->right (rw.assms->hypbox x)))
                  (force (rw.assmsp x)))
             (equal (rw.assms->contradiction x)
                    nil)))

  (defthm forcing-rw.eqtracep-of-rw.assms->contradiction
    (implies (force (and (rw.assmsp x)
                         (rw.assms->contradiction x)))
             (equal (rw.eqtracep (rw.assms->contradiction x))
                    t)))

  (defthm forcing-rw.eqtrace-contradictionp-of-rw.assms->contradiction
    (implies (force (and (rw.assmsp x)
                         (rw.assms->contradiction x)))
             (equal (rw.eqtrace-contradictionp (rw.assms->contradiction x))
                    t)))

  (defthm forcing-rw.eqtrace-okp-of-rw.assms->contradiction-and-rw.assms->hypbox
    (implies (force (and (rw.assmsp x)
                         (rw.assms->contradiction x)))
             (equal (rw.eqtrace-okp (rw.assms->contradiction x) (rw.assms->hypbox x))
                    t)))

  (defthm forcing-logic.term-listp-of-rw.assms->trueterms
    (implies (force (rw.assmsp x))
             (equal (logic.term-listp (rw.assms->trueterms x))
                    t)))

  (defthm forcing-logic.term-list-atblp-of-rw.assms->trueterms
    (implies (force (rw.assms-atblp x atbl))
             (equal (logic.term-list-atblp (rw.assms->trueterms x) atbl)
                    t)))

  (defthm forcing-rw.assmctrlp-of-rw.assms->ctrl
    (implies (force (rw.assmsp x))
             (equal (rw.assmctrlp (rw.assms->ctrl x))
                    t)))

  (defthm forcing-equal-of-rw.assms-one
    (implies (force (rw.assmsp x))
             (equal (equal x (rw.assms hypbox contradiction eqdatabase trueterms ctrl))
                    (and (equal (rw.assms->hypbox x) hypbox)
                         (equal (rw.assms->contradiction x) contradiction)
                         (equal (rw.assms->eqdatabase x) eqdatabase)
                         (equal (rw.assms->trueterms x) trueterms)
                         (equal (rw.assms->ctrl x) ctrl)))))

  (defthm forcing-equal-of-rw.assms-two
    (implies (force (rw.assmsp x))
             (equal (equal (rw.assms hypbox contradiction eqdatabase trueterms ctrl) x)
                    (and (equal (rw.assms->hypbox x) hypbox)
                         (equal (rw.assms->contradiction x) contradiction)
                         (equal (rw.assms->eqdatabase x) eqdatabase)
                         (equal (rw.assms->trueterms x) trueterms)
                         (equal (rw.assms->ctrl x) ctrl)
                         ))))

  (defthm rw.assms-atblp-of-nil
    (equal (rw.assms-atblp nil atbl)
           t)))

(deflist rw.assms-listp (x)
  (rw.assmsp x)
  :elementp-of-nil nil
  :guard t)

(deflist rw.assms-list-atblp (x atbl)
  (rw.assms-atblp x atbl)
  :elementp-of-nil t
  :guard (and (rw.assms-listp x)
              (logic.arity-tablep atbl)))



(definlined rw.empty-eqdatabase ()
  (declare (xargs :guard t))
  (rw.eqdatabase nil nil nil))

(in-theory (disable (:e rw.empty-eqdatabase)))

(encapsulate
 ()
 (local (in-theory (enable rw.empty-eqdatabase
                           rw.eqdatabase-atblp
                           rw.eqdatabase-okp)))

 (defthm rw.eqdatabasep-of-rw.empty-eqdatabase
   (equal (rw.eqdatabasep (rw.empty-eqdatabase))
          t))

 (defthm rw.eqdatabase-atblp-of-rw.empty-eqdatabase
   (equal (rw.eqdatabase-atblp (rw.empty-eqdatabase) atbl)
          t))

 (defthm rw.eqdatabase-okp-of-rw.empty-eqdatabase
   (equal (rw.eqdatabase-okp (rw.empty-eqdatabase) box)
          t))

 (defthm rw.eqdatabase->equalsets-of-rw.empty-eqdatabase
   (equal (rw.eqdatabase->equalsets (rw.empty-eqdatabase))
          nil))

 (defthm rw.eqdatabase->contradiction-of-rw.empty-eqdatabase
   (equal (rw.eqdatabase->contradiction (rw.empty-eqdatabase))
          nil)))



(definlined rw.empty-assms (ctrl)
  (declare (xargs :guard (rw.assmctrlp ctrl)))
  (rw.assms (rw.hypbox nil nil)
            nil
            (rw.empty-eqdatabase)
            nil
            ctrl))

(in-theory (disable (:e rw.empty-assms)))

(encapsulate
 ()
 (local (in-theory (enable rw.empty-assms)))

 (defthm rw.assmsp-of-rw.empty-assms
   (implies (force (rw.assmctrlp ctrl))
            (equal (rw.assmsp (rw.empty-assms ctrl))
                   t)))

 (defthm rw.assms-atblp-of-rw.empty-assms
   (equal (rw.assms-atblp (rw.empty-assms ctrl) atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.assms-atblp))))

 (defthm rw.assms->hypbox-of-rw.empty-assms
   (equal (rw.assms->hypbox (rw.empty-assms ctrl))
          (rw.hypbox nil nil)))

 (defthm rw.assms->contradiction-of-rw.empty-assms
   (equal (rw.assms->contradiction (rw.empty-assms ctrl))
          nil))

 (defthm rw.assms->eqdatabase-of-rw.empty-assms
   (equal (rw.assms->eqdatabase (rw.empty-assms ctrl))
          (rw.empty-eqdatabase)))

 (defthm rw.assms->trueterms-of-rw.empty-assms
   (equal (rw.assms->trueterms (rw.empty-assms ctrl))
          nil))

 (defthm rw.assms->ctrl-of-rw.empty-assms
   (equal (rw.assms->ctrl (rw.empty-assms ctrl))
          ctrl)))





;; MAKING ASSUMPTIONS.


(defthm rw.eqset-atblp-when-not-consp
  ;; BOZO find me a proper home
  (implies (not (consp x))
           (equal (rw.eqset-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqset-atblp
                                  rw.eqset->tail)
                                 ((:e ACL2::force))))))

(defthm forcing-rw.eqset-atblp-of-rw.find-relevant-set
  ;; BOZO find me a proper home
  (implies (force (rw.eqset-list-atblp sets atbl))
           (equal (rw.eqset-atblp (rw.find-relevant-eqset term sets) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.find-relevant-eqset))))



(defsection rw.assume-left

  (definlined rw.assume-left (nhyp assms)
    (declare (xargs :guard (and (logic.termp nhyp)
                                (rw.assmsp assms))
                    :verify-guards nil))
    (let* ((hypbox     (rw.assms->hypbox assms))
           (eqdb       (rw.assms->eqdatabase assms))
           (new-hypbox (rw.hypbox (cons nhyp (rw.hypbox->left hypbox))
                                  (rw.hypbox->right hypbox)))
           (ctrl       (rw.assms->ctrl assms))
           (new-eqdb   (rw.eqdatabase-extend nhyp eqdb
                                             (rw.assmctrl->primaryp ctrl)
                                             (rw.assmctrl->secondaryp ctrl)
                                             (rw.assmctrl->directp ctrl)
                                             (rw.assmctrl->negativep ctrl)))
           (cont       (rw.eqdatabase->contradiction new-eqdb))
           ;; We considered using the iff-t set, but found negating the equal-nil set to
           ;; be a better bet since it gives us (not x) terms as well.  Is this a bug
           ;; with our iff sets, or do we handle this?
           (false-set  (rw.find-relevant-eqset ''nil (rw.eqdatabase->equalsets new-eqdb)))
           (trueterms  (if false-set
                           (clause.smart-negate-list (rw.eqset->rhses false-set))
                         nil)))
      (rw.assms new-hypbox cont new-eqdb trueterms ctrl)))

  (defthmd lemma-for-rw.assume-left
    (implies (and (force (rw.assmsp assms))
                  (force (logic.termp nhyp)))
             (equal (rw.eqdatabase-okp (rw.assms->eqdatabase assms)
                                       (rw.hypbox (cons nhyp (rw.hypbox->left (rw.assms->hypbox assms)))
                                                  (rw.hypbox->right (rw.assms->hypbox assms))))
                    t))
    :hints(("Goal"
            :in-theory (disable rw.eqdatabase-okp-in-extended-hypbox)
            :use ((:instance rw.eqdatabase-okp-in-extended-hypbox
                             (sub (rw.assms->hypbox assms))
                             (sup (rw.hypbox (cons nhyp (rw.hypbox->left (rw.assms->hypbox assms)))
                                             (rw.hypbox->right (rw.assms->hypbox assms))))
                             (x (rw.assms->eqdatabase assms)))))))

  (local (in-theory (enable rw.assume-left
                            lemma-for-rw.assume-left)))

  (verify-guards rw.assume-left
                 :hints(("Goal" :in-theory (enable rw.eqtrace-formula))))

  (defthm forcing-rw.assmsp-of-rw.assume-left
    (implies (force (and (logic.termp nhyp)
                         (rw.assmsp assms)))
             (equal (rw.assmsp (rw.assume-left nhyp assms))
                    t)))

  (defthm forcing-rw.assms-atblp-of-rw.assume-left
    (implies (force (and (logic.termp nhyp)
                         (logic.term-atblp nhyp atbl)
                         (rw.assmsp assms)
                         (rw.assms-atblp assms atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.assms-atblp (rw.assume-left nhyp assms) atbl)
                    t)))

  (defthm rw.assms->hypbox-of-rw.assume-left
    (equal (rw.assms->hypbox (rw.assume-left nhyp assms))
           (rw.hypbox (cons nhyp (rw.hypbox->left (rw.assms->hypbox assms)))
                      (rw.hypbox->right (rw.assms->hypbox assms))))))




(defsection rw.assume-right

  (definlined rw.assume-right (nhyp assms)
    (declare (xargs :guard (and (logic.termp nhyp)
                                (rw.assmsp assms))
                    :verify-guards nil))
    (let* ((hypbox     (rw.assms->hypbox assms))
           (eqdb       (rw.assms->eqdatabase assms))
           (new-hypbox (rw.hypbox (rw.hypbox->left hypbox)
                                  (cons nhyp (rw.hypbox->right hypbox))))
           (ctrl       (rw.assms->ctrl assms))
           (new-eqdb   (rw.eqdatabase-extend nhyp eqdb
                                             (rw.assmctrl->primaryp ctrl)
                                             (rw.assmctrl->secondaryp ctrl)
                                             (rw.assmctrl->directp ctrl)
                                             (rw.assmctrl->negativep ctrl)))
           (cont       (rw.eqdatabase->contradiction new-eqdb))
           (false-row  (rw.find-relevant-eqset ''nil (rw.eqdatabase->equalsets new-eqdb)))
           (trueterms  (if false-row
                           (clause.smart-negate-list (rw.eqset->rhses false-row))
                         nil)))
      (rw.assms new-hypbox cont new-eqdb trueterms ctrl)))

  (defthmd lemma-for-rw.assume-right
    (implies (and (force (rw.assmsp assms))
                  (force (logic.termp nhyp)))
             (equal (rw.eqdatabase-okp (rw.assms->eqdatabase assms)
                                       (rw.hypbox (rw.hypbox->left (rw.assms->hypbox assms))
                                                  (cons nhyp (rw.hypbox->right (rw.assms->hypbox assms)))))
                    t))
    :hints(("Goal"
            :in-theory (disable rw.eqdatabase-okp-in-extended-hypbox)
            :use ((:instance rw.eqdatabase-okp-in-extended-hypbox
                             (sub (rw.assms->hypbox assms))
                             (sup (rw.hypbox (rw.hypbox->left (rw.assms->hypbox assms))
                                             (cons nhyp (rw.hypbox->right (rw.assms->hypbox assms)))))
                             (x (rw.assms->eqdatabase assms)))))))

  (local (in-theory (enable rw.assume-right
                            lemma-for-rw.assume-right)))

  (verify-guards rw.assume-right)

  (defthm forcing-rw.assmsp-of-rw.assume-right
    (implies (force (and (logic.termp nhyp)
                         (rw.assmsp assms)))
             (equal (rw.assmsp (rw.assume-right nhyp assms))
                    t)))

  (defthm forcing-rw.assms-atblp-of-rw.assume-right
    (implies (force (and (logic.termp nhyp)
                         (logic.term-atblp nhyp atbl)
                         (rw.assmsp assms)
                         (rw.assms-atblp assms atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.assms-atblp (rw.assume-right nhyp assms) atbl)
                    t)))

  (defthm rw.assms->hypbox-of-rw.assume-right
    (equal (rw.assms->hypbox (rw.assume-right nhyp assms))
           (rw.hypbox (rw.hypbox->left (rw.assms->hypbox assms))
                      (cons nhyp (rw.hypbox->right (rw.assms->hypbox assms)))))
    :hints(("Goal" :in-theory (enable rw.assume-right)))))



(defsection rw.assume-left-list

  (defund rw.assume-left-list (nhyps assms)
    (declare (xargs :guard (and (logic.term-listp nhyps)
                                (rw.assmsp assms))))
    (if (consp nhyps)
        (rw.assume-left (car nhyps)
                        (rw.assume-left-list (cdr nhyps) assms))
      assms))

  (defthm rw.assume-left-list-when-not-consp
    (implies (not (consp nhyps))
             (equal (rw.assume-left-list nhyps assms)
                    assms))
    :hints(("Goal" :in-theory (enable rw.assume-left-list))))

  (defthm rw.assume-left-list-of-cons
    (equal (rw.assume-left-list (cons nhyp nhyps) assms)
           (rw.assume-left nhyp (rw.assume-left-list nhyps assms)))
    :hints(("Goal" :in-theory (enable rw.assume-left-list))))

  (defthm forcing-rw.assmsp-of-rw.assume-left-list
    (implies (force (and (logic.term-listp nhyps)
                         (rw.assmsp assms)))
             (equal (rw.assmsp (rw.assume-left-list nhyps assms))
                    t))
    :hints(("Goal" :induct (cdr-induction nhyps))))

  (defthm forcing-rw.assms-atblp-of-rw.assume-left-list
    (implies (force (and (logic.term-listp nhyps)
                         (logic.term-list-atblp nhyps atbl)
                         (rw.assmsp assms)
                         (rw.assms-atblp assms atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.assms-atblp (rw.assume-left-list nhyps assms) atbl)
                    t))
    :hints(("Goal" :induct (cdr-induction nhyps))))

  (defthm forcing-rw.assms->nhyps-of-rw.assume-left-list
    (implies (force (and (logic.term-listp nhyps)
                         (rw.assmsp assms)))
             (equal (rw.assms->hypbox (rw.assume-left-list nhyps assms))
                    (rw.hypbox (app nhyps (rw.hypbox->left (rw.assms->hypbox assms)))
                               (rw.hypbox->right (rw.assms->hypbox assms)))))
    :hints(("Goal" :induct (cdr-induction nhyps)))))




(defsection rw.assume-right-list

  (defund rw.assume-right-list (nhyps assms)
    (declare (xargs :guard (and (logic.term-listp nhyps)
                                (rw.assmsp assms))))
    (if (consp nhyps)
        (rw.assume-right (car nhyps)
                         (rw.assume-right-list (cdr nhyps) assms))
      assms))

  (defthm rw.assume-right-list-when-not-consp
    (implies (not (consp nhyps))
             (equal (rw.assume-right-list nhyps assms)
                    assms))
    :hints(("Goal" :in-theory (enable rw.assume-right-list))))

  (defthm rw.assume-right-list-of-cons
    (equal (rw.assume-right-list (cons nhyp nhyps) assms)
           (rw.assume-right nhyp (rw.assume-right-list nhyps assms)))
    :hints(("Goal" :in-theory (enable rw.assume-right-list))))

  (defthm forcing-rw.assmsp-of-rw.assume-right-list
    (implies (force (and (logic.term-listp nhyps)
                         (rw.assmsp assms)))
             (equal (rw.assmsp (rw.assume-right-list nhyps assms))
                    t))
    :hints(("Goal" :induct (cdr-induction nhyps))))

  (defthm forcing-rw.assms-atblp-of-rw.assume-right-list
    (implies (force (and (logic.term-listp nhyps)
                         (logic.term-list-atblp nhyps atbl)
                         (rw.assmsp assms)
                         (rw.assms-atblp assms atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.assms-atblp (rw.assume-right-list nhyps assms) atbl)
                    t))
    :hints(("Goal" :induct (cdr-induction nhyps))))

  (defthm forcing-rw.assms->hypbox-right-of-rw.assume-right-list
    (implies (force (and (logic.term-listp nhyps)
                         (rw.assmsp assms)))
             (equal (rw.assms->hypbox (rw.assume-right-list nhyps assms))
                    (rw.hypbox (rw.hypbox->left (rw.assms->hypbox assms))
                               (app nhyps (rw.hypbox->right (rw.assms->hypbox assms))))))
    :hints(("Goal" :induct (cdr-induction nhyps)))))





(definlined rw.assms-emptyp (assms)
  (declare (xargs :guard (rw.assmsp assms)))
  (let ((hypbox (rw.assms->hypbox assms)))
    (and (not (rw.hypbox->left hypbox))
         (not (rw.hypbox->right hypbox)))))

(defthm booleanp-of-rw.assms-emptyp
  (equal (booleanp (rw.assms-emptyp assms))
         t)
  :hints(("Goal" :in-theory (enable rw.assms-emptyp))))

(defthm rw.assms-emptyp-of-rw.empty-assms
  (equal (rw.assms-emptyp (rw.empty-assms ctrl))
         t)
  :hints(("Goal" :in-theory (enable rw.assms-emptyp))))



(definlined rw.assms-formula (assms)
  (declare (xargs :guard (and (rw.assmsp assms)
                              (not (rw.assms-emptyp assms)))
                  :guard-hints (("Goal" :in-theory (enable rw.assms-emptyp)))))
  (rw.hypbox-formula (rw.assms->hypbox assms)))

(defthm forcing-logic.formulap-of-rw.assms-formula
  (implies (force (and (rw.assmsp assms)
                       (not (rw.assms-emptyp assms))))
           (equal (logic.formulap (rw.assms-formula assms))
                  t))
  :hints(("Goal" :in-theory (enable rw.assms-formula rw.assms-emptyp))))

(defthm forcing-logic.formula-atblp-of-rw.assms-formula
  (implies (force (and (rw.assmsp assms)
                       (rw.assms-atblp assms atbl)
                       (not (rw.assms-emptyp assms))))
           (equal (logic.formula-atblp (rw.assms-formula assms) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.assms-formula rw.assms-emptyp))))
