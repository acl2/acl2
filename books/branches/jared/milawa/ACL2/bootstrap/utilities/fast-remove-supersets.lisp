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
(include-book "extended-subsets")
(include-book "mergesort")
(%interactive)


(%deflist ordered-list-listp (x)
          (ordered-listp x))

(%defprojection :list (mergesort-list x)
                :element (mergesort x)
                :nil-preservingp t)

(%autoprove ordered-list-listp-of-mergesort-list
            (%cdr-induction x))

(%autoprove superset-of-somep-of-mergesort-left
            (%cdr-induction x))

(%autoprove superset-of-somep-of-mergesort-list-right
            (%cdr-induction x))


(%autoadmit fast-superset-of-somep)

(%autoprove fast-superset-of-somep-when-not-consp
            (%restrict default fast-superset-of-somep (equal x 'x)))

(%autoprove fast-superset-of-somep-of-cons
            (%restrict default fast-superset-of-somep (equal x '(cons b x))))

(%autoprove fast-superset-of-somep-removal
            (%cdr-induction x)
            (%enable default
                     fast-superset-of-somep-when-not-consp
                     fast-superset-of-somep-of-cons))



(%autoadmit fast-remove-supersets1)

(%autoprove fast-remove-supersets1-when-not-consp
            (%restrict default fast-remove-supersets1 (equal todo-sorted 'todo-sorted)))

(%autoprove fast-remove-supersets1-of-cons
            (%restrict default fast-remove-supersets1 (equal todo-sorted '(cons a todo-sorted))))

(%autoprove fast-remove-supersets1-removal
            (%autoinduct remove-supersets1 todo done)
            (%enable default
                     fast-remove-supersets1-when-not-consp
                     fast-remove-supersets1-of-cons))




(%autoadmit cdr-10-times)
(%autoadmit cdr-50-times)
(%autoadmit cdr-250-times)
(%autoadmit len-over-250p)
(%autoadmit some-len-over-250p)

(%autoadmit fast-remove-supersets)

(%autoprove fast-remove-supersets-removal
            (%enable default
                     fast-remove-supersets
                     remove-supersets)
            (%disable default
                      fast-remove-supersets1-removal
                      [outside]fast-remove-supersets1-removal)
            (%use (%instance (%thm fast-remove-supersets1-removal)
                             (todo x)
                             (done nil))))

(%ensure-exactly-these-rules-are-missing "../../utilities/fast-remove-supersets")