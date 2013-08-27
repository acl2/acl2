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
(include-book "hacks")
(include-book "equal")
(%interactive)



(local (%noexec cons))

(local (%enable default
                bust-up-logic.function-args-expensive
                bust-up-cdr-of-logic.function-args-expensive
                bust-up-cdr-of-cdr-of-logic.function-args-expensive))


(%autoadmit definition-of-iff)
(%noexec definition-of-iff)

(%deftheorem theorem-iff-lhs-false)
(%deftheorem theorem-iff-lhs-true)
(%deftheorem theorem-iff-rhs-false)
(%deftheorem theorem-iff-rhs-true)

(%deftheorem theorem-iff-both-true)
(%deftheorem theorem-iff-both-false)
(%deftheorem theorem-iff-true-false)
(%deftheorem theorem-iff-false-true)

(%deftheorem theorem-iff-t-when-not-nil)
(%defderiv build.iff-t-from-not-pequal-nil)
(%defderiv build.disjoined-iff-t-from-not-pequal-nil)

(%deftheorem theorem-iff-t-when-nil)
(%defderiv build.not-pequal-nil-from-iff-t)
(%defderiv build.disjoined-not-pequal-nil-from-iff-t)

(%deftheorem theorem-iff-nil-when-nil)
(%deftheorem theorem-iff-nil-when-not-nil)


;; (%deftheorem theorem-iff-t-when-not-nil)
;; (%defderiv build.iff-t-from-not-pequal-nil)
;; (%defderiv build.disjoined-iff-t-from-not-pequal-nil)


;; (%defderiv build.pequal-nil-from-iff-nil)
;; (%defderiv build.disjoined-pequal-nil-from-iff-nil)

(%deftheorem theorem-iff-nil-or-t)
(%deftheorem theorem-reflexivity-of-iff)
(%deftheorem theorem-symmetry-of-iff)

(%defderiv build.iff-t-from-not-nil)
(%defderiv build.disjoined-iff-t-from-not-nil)
(%defderiv build.iff-reflexivity)
(%defderiv build.commute-iff)
(%defderiv build.disjoined-commute-iff)


(%deftheorem theorem-iff-congruence-lemma)
(%deftheorem theorem-iff-congruence-lemma-2)

(%deftheorem theorem-iff-congruent-if-1)
(%deftheorem theorem-iff-congruent-iff-2)
(%deftheorem theorem-iff-congruent-iff-1)

(%deftheorem theorem-transitivity-of-iff)
(%defderiv build.transitivity-of-iff)
(%defderiv build.disjoined-transitivity-of-iff)

(%deftheorem theorem-iff-from-pequal)
(%defderiv build.iff-from-pequal)
(%defderiv build.disjoined-iff-from-pequal)

(%deftheorem theorem-iff-from-equal)
(%defderiv build.iff-from-equal)
(%defderiv build.disjoined-iff-from-equal)

(%autoadmit build.equiv-reflexivity)


;; EOF














;; old junk

;; (%deftheorem theorem-iff-when-not-nil-and-not-nil)
;; (%deftheorem theorem-iff-when-not-nil-and-nil)
;; (%deftheorem theorem-iff-when-nil-and-not-nil)
;; (%deftheorem theorem-iff-when-nil-and-nil)
;; (%deftheorem theorem-iff-of-nil)
;; (%deftheorem theorem-iff-of-t)

;; (%deftheorem theorem-iff-normalize-t)
;; (%deftheorem theorem-iff-normalize-nil)


;; (%defderiv build.iff-reflexivity)


;; (%deftheorem theorem-iff-from-pequal)
;; (%defderiv build.iff-from-pequal)
;; (%defderiv build.disjoined-iff-from-pequal)

;; (%deftheorem theorem-iff-from-equal)
;; (%defderiv build.iff-from-equal)
;; (%defderiv build.disjoined-iff-from-equal)
;; (%defderiv build.not-equal-from-not-iff)



;; (%defderiv build.disjoined-not-equal-from-not-iff)

;; (%deftheorem theorem-iff-with-nil-or-t)
;; (%deftheorem theorem-iff-nil-or-t)

;; (%defderiv build.iff-t-from-not-nil)
;; (%defderiv build.disjoined-iff-t-from-not-nil)
;; (%defderiv build.iff-nil-from-not-t)
;; (%defderiv build.disjoined-iff-nil-from-not-t)



;; (%defderiv build.commute-iff)
;; (%defderiv build.disjoined-commute-iff)


;; (%deftheorem theorem-transitivity-two-of-iff)
;; (%deftheorem theorem-transitivity-of-iff)

;; (%defderiv build.transitivity-of-iff)
;; (%defderiv build.disjoined-transitivity-of-iff)

;; (%deftheorem theorem-iff-of-if-x-t-nil)

