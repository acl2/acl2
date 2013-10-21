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
(include-book "aux-split")
(%interactive)


(local (%disable default
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-term/formula-inference
                 expensive-subsetp-rules
                 unusual-consp-rules))

(%autoadmit clause.aux-limsplit)

(%autoprove true-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

;; (%autoprove consp-of-clause.aux-limsplit
;;             (%autoinduct clause.aux-limsplit)
;;             (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

;; (%autoprove clause.aux-limsplit-under-iff
;;             (%autoinduct clause.aux-limsplit)
;;             (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

(%autoprove forcing-term-list-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

(%autoprove forcing-term-list-list-atblp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

(%autoprove forcing-cons-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))





;; (%autoprove clause.aux-limsplit-when-double-negative
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-1
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-2
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-3
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-4
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-1
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-2
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-3
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-4
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-not-consp
;;             (%restrict default clause.aux-limsplit (equal todo 'todo)))

;; (%autoprove clause.aux-limsplit-when-zp
;;             (%restrict default clause.aux-limsplit (equal todo 'todo)))

;; (%create-theory clause.aux-limsplit-openers)
;; (%enable clause.aux-limsplit-openers
;;          clause.aux-limsplit-when-double-negative
;;          clause.aux-limsplit-when-negative-1
;;          clause.aux-limsplit-when-negative-1
;;          clause.aux-limsplit-when-negative-2
;;          clause.aux-limsplit-when-negative-3
;;          clause.aux-limsplit-when-negative-4
;;          clause.aux-limsplit-when-positive-1
;;          clause.aux-limsplit-when-positive-2
;;          clause.aux-limsplit-when-positive-3
;;          clause.aux-limsplit-when-positive-4
;;          clause.aux-limsplit-when-not-consp
;;          clause.aux-limsplit-when-zp)

