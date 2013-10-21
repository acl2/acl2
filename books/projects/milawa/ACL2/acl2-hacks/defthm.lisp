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

#|

;; this isn't needed anymore because we have no-fertilize.lisp instead.
;; we have added defthm and defthmd to the milawa package now.

(defund mangle-hints2 (x)
  ;; X should be a list of instructions to attach to a specific goal, i.e., X
  ;; might be (:in-theory ... :induct ... :do-not ...).  If no :do-not key is
  ;; provided, we add :do-not '(generalize fertilize).
  (declare (xargs :guard (true-listp x)))
  (if (member :do-not x)
      x
    (list* :do-not ''(generalize fertilize) x)))

(defund mangle-hints1 (x)
  ;; X should be a list of hints such as (("Goal" ...) ("Subgoal 1" ...)).  We
  ;; find the goal hint and mangle2 it by adding :do-not '(generalize
  ;; fertilize).  If no goal hint exists, we insert one.
  (declare (xargs :guard t))
  (if (consp x)
      (if (and (consp (car x))
               (stringp (car (car x)))
               (standard-char-listp (coerce (car (car x)) 'list))
               (equal (string-downcase (car (car x))) "goal")
               (true-listp (car x)))
          (cons (cons "Goal" (mangle-hints2 (cdr (car x)))) (cdr x))
        (cons (car x) (mangle-hints1 (cdr x))))
    (cons (cons "Goal" (mangle-hints2 nil))
          nil)))

(defund mangle-hints (x)
  ;; X should be an argument list given to defthm, e.g., something like
  ;; ((implies hyps concl) :rule-classes ... :hints ... :otf-flg t).  We find
  ;; the :hints argument and augment it with our :do-not instruction, or if
  ;; there are no hints we insert our do-not hint on "Goal".
  (declare (xargs :guard t))
  (if (consp x)
      (if (and (equal (car x) :hints)
               (consp (cdr x)))
          (list* :hints
                 (mangle-hints1 (second x))
                 (cddr x))
        (cons (car x) (mangle-hints (cdr x))))
    (list* :hints
           (mangle-hints1 nil)
           nil)))

(defmacro MILAWA::thm (&rest args)
  `(ACL2::thm ,@(mangle-hints args)))

(defmacro MILAWA::defthm (&rest args)
  `(ACL2::defthm ,@(mangle-hints args)))

(defmacro MILAWA::defthmd (&rest args)
  `(ACL2::defthmd ,@(mangle-hints args)))



|#