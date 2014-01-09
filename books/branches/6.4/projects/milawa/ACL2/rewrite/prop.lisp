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
(include-book "../build/prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defderiv rw.crewrite-twiddle-bldr
  :derive (v B (v A C))
  :from   ((proof x (v (v A B) C)))
  :proof  (@derive
           ((v (v A B) C)    (@given x))
           ((v C (v A B))    (build.commute-or @-))
           ((v (v C A) B)    (build.associativity @-))
           ((v B (v C A))    (build.commute-or @-))
           ((v B (v A C))    (build.disjoined-commute-or @-))))

(defderiv rw.crewrite-twiddle2-lemma
  :derive (v B (v (v C D) A))
  :from   ((proof x (v (v (v A B) C) D)))
  :proof  (@derive
           ((v (v (v A B) C) D)    (@given x))
           ((v D (v (v A B) C))    (build.commute-or @-))
           ((v (v D (v A B)) C)    (build.associativity @-))
           ((v C (v D (v A B)))    (build.commute-or @-))
           ((v (v C D) (v A B))    (build.associativity @-))
           ((v (v (v C D) A) B)    (build.associativity @-))
           ((v B (v (v C D) A))    (build.commute-or @-))))

(defderiv rw.crewrite-twiddle2-bldr
  :derive (v (v B C) (v A D))
  :from   ((proof x (v (v (v A B) C) D)))
  :proof  (@derive
           ((v (v (v A B) C) D)    (@given x))
           ((v B (v (v C D) A))    (rw.crewrite-twiddle2-lemma @-))
           ((v B (v C (v D A)))    (build.disjoined-right-associativity @-))
           ((v (v B C) (v D A))    (build.associativity @-))
           ((v (v B C) (v A D))    (build.disjoined-commute-or @-))))
