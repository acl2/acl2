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
(include-book "utilities-3")
(%interactive)



(%autoadmit tuplep)

(defmacro %tuplep-induct (n x)
  `(%induct (nfix ,n)
            ((zp ,n)
             nil)
            ((not (zp ,n))
             (((,n (- ,n 1))
               (,x (cdr ,x)))))))

(%autoprove tuplep-when-not-consp
            (%restrict default tuplep (equal n 'n)))

(%autoprove tuplep-when-zp
            (%restrict default tuplep (equal n 'n)))

(%autoprove tuplep-of-cons
            (%restrict default tuplep (equal n 'n)))

(%autoprove booleanp-of-tuplep
            (%tuplep-induct n x))

(%autoprove true-listp-when-tuplep
            (%tuplep-induct n x))

(%autoprove len-when-tuplep
            (%tuplep-induct n x))

(defthm tuplep-of-len
  ;; BOZO move to utilities
  (equal (tuplep (len x) x)
         (true-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(%autoprove tuplep-of-len
            (%cdr-induction x)
            (%restrict default tuplep (equal x 'x)))

(%autoprove tuplep-when-true-listp
            (%tuplep-induct n x))

(%autoprove consp-of-cdr-when-tuplep-2-cheap)
(%autoprove consp-of-cdr-when-tuplep-3-cheap)
(%autoprove consp-of-cdr-of-cdr-when-tuplep-3-cheap)
