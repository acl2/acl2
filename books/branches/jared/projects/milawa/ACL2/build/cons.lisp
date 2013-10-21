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
(include-book "pequal-list")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "cons.tex")

(deftheorem theorem-cons-is-not-nil
  :derive (!= (cons x y) nil)
  :proof  (@derive
           ((v (= (symbolp x) nil)          (= (consp x) nil))              (build.axiom (axiom-disjoint-symbols-and-conses)))
           ((v (= (symbolp (cons x y)) nil) (= (consp (cons x y)) nil))     (build.instantiation @- (@sigma (x . (cons x y)))))
           ((v (= (consp (cons x y)) nil)   (= (symbolp (cons x y)) nil))   (build.commute-or @-)                                 *1)
           ((= (consp (cons x y)) t)                                        (build.axiom (axiom-consp-of-cons)))
           ((!= (consp (cons x y)) nil)                                     (build.not-nil-from-t @-))
           ((= (symbolp (cons x y)) nil)                                    (build.modus-ponens-2 @- *1))
           ((!= (symbolp (cons x y)) t)                                     (build.not-t-from-nil @-))
           ((!= t (symbolp (cons x y)))                                     (build.commute-not-pequal @-))
           ((= (symbolp nil) t)                                             (build.base-eval '(symbolp 'nil)))
           ((!= (symbolp nil) (symbolp (cons x y)))                         (build.substitute-into-not-pequal @-- @-))
           ((!= (symbolp (cons x y)) (symbolp nil))                         (build.commute-not-pequal @-)                         *2)
           ((v (!= (cons x y) nil) (= (cons x y) nil))                      (build.propositional-schema (@formula (= (cons x y) nil))))
           ((v (!= (cons x y) nil) (= (symbolp (cons x y)) (symbolp nil)))  (build.disjoined-pequal-by-args 'symbolp (@formula (!= (cons x y) nil)) (list @-)))
           ((v (= (symbolp (cons x y)) (symbolp nil)) (!= (cons x y) nil))  (build.commute-or @-))
           ((!= (cons x y) nil)                                             (build.modus-ponens-2 *2 @-)))
  :minatbl ((cons . 2)
            (consp . 1)
            (symbolp . 1)))

(dd.close)