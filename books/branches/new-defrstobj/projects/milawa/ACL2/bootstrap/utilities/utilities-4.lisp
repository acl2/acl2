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
(include-book "utilities-4-remove-all")
(include-book "utilities-4-disjointp")
(include-book "utilities-4-uniquep")
(include-book "utilities-4-difference")
(include-book "utilities-4-remove-duplicates")
(include-book "utilities-4-tuplep")
(include-book "utilities-4-repeat")
(include-book "utilities-4-nth")
(%interactive)



;; Extra theorems for disjointp.

(%autoprove disjointp-of-remove-all-of-remove-all-when-disjointp-right)

(%autoprove disjointp-of-remove-all-when-disjointp-left)



;; Extra theorems for uniquep.

(%autoprove uniquep-of-app
            (%cdr-induction x))

(%autoprove uniquep-of-rev
            (%cdr-induction x))

(%autoprove uniquep-of-remove-all-when-uniquep
            (%cdr-induction x))



;; Extra theorems for difference.

(%autoprove uniquep-of-difference-when-uniquep
            (%cdr-induction x))

(%autoprove disjointp-of-difference-with-y
            (%cdr-induction x))

(%autoprove disjointp-of-difference-with-y-alt
            (%cdr-induction x))



;; Extra theorems for remove-duplicates.

(%autoprove uniquep-of-remove-duplicates
            (%cdr-induction x))

(%autoprove remove-duplicates-of-difference
            (%cdr-induction x))

(%autoprove remove-duplicates-when-unique
            (%cdr-induction x))

(%autoprove app-of-remove-duplicates-with-unique-and-disjoint
            (%cdr-induction x))

(%autoprove remove-duplicates-of-remove-all
            (%cdr-induction x))

(%autoprove subsetp-of-remove-all-of-remove-duplicates)


;; Extra theorems for nth.

(%autoprove equal-of-nths-when-uniquep
            ;; This proof is pretty cool.  It has really improved over time as my
            ;; tactics have gotten better.
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((and (consp x)
                           (or (zp m)
                               (zp n)))
                      nil)
                     ((and (consp x)
                           (not (zp m))
                           (not (zp n)))
                      (((x (cdr x))
                        (n (- n 1))
                        (m (- m 1))))))
            (%restrict default nth (or (equal n 'n) (equal n 'm) (equal n ''0) (equal n ''1))))








