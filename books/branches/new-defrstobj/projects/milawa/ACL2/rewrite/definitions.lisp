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
(include-book "../logic/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Function definitions are formulas of the form
;;
;;  (fn arg1 ... argn) = body
;;
;; Where fn is some function symbol, arg1, ..., argn are a list of distinct
;; variables, and body is a term which only mentions the variables arg1, ...,
;; argn.
;;
;; BOZO shouldn't this be guarded with formulap?  I guess for now
;; we'll leave it alone. It's sort of strange that we're re-using formulas
;; instead of writing a new data structure, but I guess it's simple enough.

(defund definitionp (x)
  (declare (xargs :guard t))
  (and (logic.formulap x)
       (equal (logic.fmtype x) 'pequal*)
       (let ((lhs (logic.=lhs x))
             (rhs (logic.=rhs x)))
         (and (logic.functionp lhs)
              (let ((formals (logic.function-args lhs)))
                (and (logic.variable-listp formals)
                     (uniquep formals)
                     (subsetp (logic.term-vars rhs) formals)))))))

(defthm booleanp-of-definitionp
  (equal (booleanp (definitionp x))
         t)
  :hints(("Goal" :in-theory (enable definitionp))))

(defthm logic.formulap-when-definitionp
  (implies (definitionp x)
           (equal (logic.formulap x)
                  t))
  :hints(("Goal" :in-theory (enable definitionp))))

(defthm logic.fmtype-when-definitionp
  (implies (definitionp x)
           (equal (logic.fmtype x) 'pequal*))
  :hints(("Goal" :in-theory (enable definitionp))))

(defthm logic.functionp-of-logic.=lhs-when-definitionp
  (implies (definitionp x)
           (equal (logic.functionp (logic.=lhs x))
                  t))
  :hints(("Goal" :in-theory (enable definitionp))))

(defthm logic.variable-listp-of-logic.function-args-of-logic.=lhs-when-definitionp
  (implies (definitionp x)
           (equal (logic.variable-listp (logic.function-args (logic.=lhs x)))
                  t))
  :hints(("Goal" :in-theory (enable definitionp))))

(defthm uniquep-of-logic.function-args-of-logic.=lhs-when-definitionp
  (implies (definitionp x)
           (equal (uniquep (logic.function-args (logic.=lhs x)))
                  t))
  :hints(("Goal" :in-theory (enable definitionp))))

(defthm subsetp-of-logic.term-vars-of-logic.=rhs-when-definitionp
  (implies (definitionp x)
           (equal (subsetp (logic.term-vars (logic.=rhs x))
                           (logic.function-args (logic.=lhs x)))
                  t))
  :hints(("Goal" :in-theory (enable definitionp))))



(deflist definition-listp (x)
  (definitionp x)
  :elementp-of-nil nil)

(defthm logic.formula-listp-when-definition-listp
  (implies (definition-listp x)
           (equal (logic.formula-listp x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defund definition-list-lookup (fn x)
  (declare (xargs :guard (and (logic.function-namep fn)
                              (definition-listp x))))
  (if (consp x)
      (if (equal fn (logic.function-name (logic.=lhs (car x))))
          (car x)
        (definition-list-lookup fn (cdr x)))
    nil))

(defthm definition-list-lookup-when-not-consp
  (implies (not (consp x))
           (equal (definition-list-lookup fn x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-list-lookup))))

(defthm definition-list-lookup-of-cons
  (equal (definition-list-lookup fn (cons a x))
         (if (equal fn (logic.function-name (logic.=lhs a)))
             a
           (definition-list-lookup fn x)))
  :hints(("Goal" :in-theory (enable definition-list-lookup))))

(defthm definitionp-of-definition-list-lookup
  (implies (force (definition-listp x))
           (equal (definitionp (definition-list-lookup fn x))
                  (if (definition-list-lookup fn x)
                      t
                    nil)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.formula-atblp-of-definition-list-lookup
  (implies (and (force (definition-listp x))
                (force (logic.formula-list-atblp x atbl)))
           (equal (logic.formula-atblp (definition-list-lookup fn x) atbl)
                  (if (definition-list-lookup fn x)
                      t
                    nil)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-definition-list-lookup
  (implies (and (definition-listp defs)
                (definition-list-lookup fn defs))
           (equal (memberp (definition-list-lookup fn defs) defs)
                  t))
  :hints(("Goal" :induct (cdr-induction defs))))

(defthm forcing-logic.fmtype-of-definition-list-lookup
  (implies (and (force (definition-listp defs))
                (definition-list-lookup name defs))
           (equal (logic.fmtype (definition-list-lookup name defs))
                  'pequal*))
  :hints(("Goal" :in-theory (enable definition-list-lookup definitionp))))

(defthm forcing-logic.function-name-of-logic.=lhs-of-definition-list-lookup
  (implies (definition-list-lookup name defs)
           (equal (logic.function-name (logic.=lhs (definition-list-lookup name defs)))
                  name))
  :hints(("Goal" :in-theory (enable definition-list-lookup))))

(defthm forcing-logic.functionp-of-logic.=lhs-of-definition-list-lookup
  (implies (and (definition-list-lookup name defs)
                (force (definition-listp defs)))
           (equal (logic.functionp (logic.=lhs (definition-list-lookup name defs)))
                  t))
  :hints(("Goal" :in-theory (enable definition-list-lookup definitionp))))
