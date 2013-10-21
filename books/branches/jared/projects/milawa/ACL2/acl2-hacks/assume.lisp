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

(in-package "ACL2")

;; assume.lisp
;;
;; We introduce a utility for sharing assumptions across theorems.
;;
;; BOZO this file should be submitted to the ACL2 distribution and removed from
;; our sources.  It should become a "misc" book.

(defdoc assume
  ":Doc-Section Events

   a system for sharing assumptions across many theorems~/

   We provide a simple table-based system for reusable assumptions.  To the
   user, this system takes on the following interface:
   ~bv[]
     (assume <term>)
        adds term to the local assumptions

     (unassume <term>)
        removes <term> from the local assumptions

     (conclude <name> <thm> :hints ... :rule-classes ...)
        like defth, but proves <thm> under the current assumptions
   ~ev[]

   For example, consider the following ACL2 rules:
   ~bv[]
     (defthm natp-of-plus
       (implies (and (natp x)
                     (natp y))
                (natp (+ x y))))

     (defthm natp-of-minus
       (implies (and (natp x)
                     (natp y)
                     (< y x))
                (natp (- x y))))
   ~ev[]

   We can convert these into the assume/conclude style as follows:
   ~ev[]
     (assume (natp x))
     (assume (natp y))
     (conclude natp-of-plus (natp (+ x y)))
     (conclude natp-of-minus (implies (< y x) (natp (- x y))))
   ~ev[]~/

   The ~c[assume] and ~c[unassume] commands are implicitly ~il[local], so you
   can use ~il[encapsulate] in addition to ~c[unassume] to limit the scope of
   your assumptions.

   The ~c[conclude] command recognizes ~c[thm]s of the following forms:
   ~bv[]
      (implies (and hyp1 ... hypN) concl)
      (implies hyp1 concl)
      concl
   ~ev[]

   It augments the <thm> by injecting the current assumptions after the last
   hyp.  That is, we produce:
   ~bv[]
     (implies (and hyp1 ... hypN assm1 ... assmK) concl)
     (implies (and hyp1 assm1 ... assmK) concl)
     (implies (and assm1 ... assmK) concl)
   ~ev[]

   We expect this to be appropriate most of the time, since shared hyps tend to
   be ``common'' sorts of things, e.g., type constraints, etc.  Meanwhile, the
   unshared hyps should tend to be more complicated and unusual, so we place
   them at the front of the rule in an effort to make ``fast failing'' rules.")


(table assume.table 'assumptions nil)

(defun assume.get-assumptions (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'assumptions (table-alist 'assume.table world))))

(defun assume.assume-fn (assm)
  `(local (table assume.table 'assumptions
                 (cons ',assm (assume.get-assumptions world)))))

(defmacro assume (assm)
  (assume.assume-fn assm))


(defun assume.unassume-fn (assm)
  (declare (xargs :mode :program))
  `(local (table assume.table 'assumptions
                 (remove-equal ',assm (assume.get-assumptions world)))))

(defmacro unassume (assm)
  (assume.unassume-fn assm))


(defun assume.conclude-fn (name thm extra-args world)
  (declare (xargs :mode :program))
  (cond ((and (consp thm)
              (equal (first thm) 'implies)
              (consp (second thm))
              (equal (first (second thm)) 'and))
         ;; Thm has the form (implies (and hyp1 ... hypN) concl)
         (let ((hyps  (cdr (second thm)))
               (concl (third thm)))
           `(defthm ,name
              (implies (and ,@(append hyps (assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        ((and (consp thm)
              (equal (first thm) 'implies))
         ;; Thm has the form (implies hyp1 concl)
         (let ((hyps  (list (second thm)))
               (concl (third thm)))
           `(defthm ,name
              (implies (and ,@(append hyps (assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        (t
         ;; Thm has the form concl
         `(defthm ,name
            (implies (and ,@(assume.get-assumptions world))
                     ,thm)
            ,@extra-args))))

(defmacro conclude (name thm &rest extra-args)
  `(make-event (assume.conclude-fn ',name ',thm ',extra-args (w state))))





(defmacro MILAWA::assume (&rest args)
  `(ACL2::assume ,@args))

(defmacro MILAWA::unassume (&rest args)
  `(ACL2::unassume ,@args))

(defun milawa-conclude-fn (name thm extra-args world)
  (declare (xargs :mode :program))
  (cond ((and (consp thm)
              (equal (first thm) 'implies)
              (consp (second thm))
              (equal (first (second thm)) 'and))
         ;; Thm has the form (implies (and hyp1 ... hypN) concl)
         (let ((hyps  (cdr (second thm)))
               (concl (third thm)))
           `(MILAWA::defthm ,name
              (implies (and ,@(ACL2::append hyps (ACL2::assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        ((and (consp thm)
              (equal (first thm) 'implies))
         ;; Thm has the form (implies hyp1 concl)
         (let ((hyps  (list (second thm)))
               (concl (third thm)))
           `(MILAWA::defthm ,name
              (implies (and ,@(ACL2::append hyps (ACL2::assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        (t
         ;; Thm has the form concl
         `(MILAWA::defthm ,name
            (implies (and ,@(ACL2::assume.get-assumptions world))
                     ,thm)
            ,@extra-args))))

(defmacro MILAWA::conclude (name thm &rest extra-args)
  `(ACL2::make-event (milawa-conclude-fn ',name ',thm ',extra-args (ACL2::w ACL2::state))))

