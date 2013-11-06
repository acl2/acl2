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
(include-book "list-list-fix")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund slow-simple-flatten (x)
  ;; Computes (simple-flatten x) very inefficiently.  There's no reason to ever
  ;; use this function.
  (declare (xargs :guard t))
  (if (consp x)
      (app (car x)
           (slow-simple-flatten (cdr x)))
    nil))

(defthm slow-simple-flatten-when-not-consp
  (implies (not (consp x))
           (equal (slow-simple-flatten x)
                  nil))
  :hints(("Goal" :in-theory (enable slow-simple-flatten))))

(defthm slow-simple-flatten-of-cons
  (equal (slow-simple-flatten (cons a x))
         (app a (slow-simple-flatten x)))
  :hints(("Goal" :in-theory (enable slow-simple-flatten))))

(defund fast-simple-flatten$ (x acc)
  ;; Computes (revappend (simple-flatten x) acc).  This is cheaper than calling
  ;; simple-flatten, saveing you one "fast-rev" call and the associated
  ;; consing.
  (declare (xargs :guard (true-listp acc)))
  (if (consp x)
      (fast-simple-flatten$ (cdr x)
                            (revappend (car x) acc))
    acc))


(defund simple-flatten (x)
  ;; Does one level of list flattening.  This won't flatten a whole tree, it'll
  ;; just condense a two-level "list of lists" into a regular, one-level list.
  ;; It takes two linear passes of consing.
  (declare (xargs :guard t))
  (fast-rev (fast-simple-flatten$ x nil)))

(defthmd lemma-for-definition-of-simple-flatten
  (implies (true-listp acc)
           (equal (fast-simple-flatten$ x acc)
                  (app (rev (slow-simple-flatten x)) acc)))
  :hints(("Goal" :in-theory (enable fast-simple-flatten$))))

(defthmd definition-of-simple-flatten
  (equal (simple-flatten x)
         (if (consp x)
             (app (car x)
                  (simple-flatten (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable simple-flatten
                                    lemma-for-definition-of-simple-flatten))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition simple-flatten))))

(defthm simple-flatten-when-not-consp
  (implies (not (consp x))
           (equal (simple-flatten x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-simple-flatten))))

(defthm simple-flatten-of-cons
  (equal (simple-flatten (cons a x))
         (app a (simple-flatten x)))
  :hints(("Goal" :in-theory (enable definition-of-simple-flatten))))

(defthm true-listp-of-simple-flatten
  (equal (true-listp (simple-flatten x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm simple-flatten-of-list-fix
  (equal (simple-flatten (list-fix x))
         (simple-flatten x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm simple-flatten-of-app
  (equal (simple-flatten (app x y))
         (app (simple-flatten x) (simple-flatten y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm simple-flatten-of-list-list-fix
  (equal (simple-flatten (list-list-fix x))
         (simple-flatten x))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm forcing-fast-simple-flatten$-removal
  (implies (force (true-listp acc))
           (equal (fast-simple-flatten$ x acc)
                  (app (rev (simple-flatten x)) acc)))
  :hints(("Goal" :in-theory (enable fast-simple-flatten$))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition fast-simple-flatten$))))




(defun fast-simple-flatten-of-domain$ (x acc)
  ;; Calculates (revappend (simple-flatten (domain x)) acc) in a single,
  ;; tail-recursive linear pass.
  (declare (xargs :guard (and (mapp x)
                              (true-listp acc))))
  (if (consp x)
      (fast-simple-flatten-of-domain$ (cdr x)
                                      (revappend (car (car x)) acc))
    acc))

(defthm fast-simple-flatten-of-domain$-removal
  (implies (force (true-listp acc))
           (equal (fast-simple-flatten-of-domain$ x acc)
                  (app (rev (simple-flatten (domain x))) acc))))



(defun fast-simple-flatten-of-range$ (x acc)
  ;; Calculates (revappend (simple-flatten (range x)) acc) in a single,
  ;; tail-recursive linear pass.
  (declare (xargs :guard (and (mapp x)
                              (true-listp acc))))
  (if (consp x)
      (fast-simple-flatten-of-range$ (cdr x)
                                     (revappend (cdr (car x)) acc))
    acc))

(defthm fast-simple-flatten-of-range$-removal
  (implies (force (true-listp acc))
           (equal (fast-simple-flatten-of-range$ x acc)
                  (app (rev (simple-flatten (range x))) acc))))

