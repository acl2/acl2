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
(include-book "deflist")
(include-book "strip-firsts")
(include-book "strip-seconds")
(include-book "strip-lens")
(%interactive)


(%deflist true-list-listp (x)
          (true-listp x))



(%deflist tuple-listp (n x)
          (tuplep n x))

(%autoprove rank-of-strip-firsts-when-tuple-listp-2
            (%cdr-induction x))

(%autoprove rank-of-strip-seconds-when-tuple-listp-2
            (%cdr-induction x))

(%autoprove strip-lens-when-tuple-listp
            (%cdr-induction x)
            (%auto)
            (%fertilize (strip-lens x2) (repeat (nfix n) (len x2))))



(%autoadmit list2-list)

(%autoprove list2-list-when-not-consp-one
            (%restrict default list2-list (equal x 'x)))

(%autoprove list2-list-when-not-consp-two
            (%restrict default list2-list (equal x 'x)))

(%autoprove list2-list-of-cons-and-cons
            (%restrict default list2-list (equal x '(cons a x))))

(%autoprove true-listp-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove true-listp-list-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove list2-list-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove list2-list-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove len-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove strip-lens-of-list2-list
            (%cdr-cdr-induction x y))


(defsection more-than-two-when-not-zero-one-or-two
  ;; This isn't needed in ACL2.  not sure why we need it.
  ;; BOZO might this have to do with our missing rule?
  (%prove (%rule more-than-two-when-not-zero-one-or-two
                 :hyps (list (%hyp (not (zp n)))
                             (%hyp (not (equal 1 n)))
                             (%hyp (not (equal 2 n))))
                 :lhs (< 2 n)
                 :rhs t))
  (%use (%instance (%thm squeeze-law-one) (b 2) (a n)))
  (%auto)
  (%qed))

(%autoprove tuple-listp-of-list2-list
            (%cdr-cdr-induction x y)
            (%enable default more-than-two-when-not-zero-one-or-two))

(%autoprove forcing-strip-firsts-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-strip-seconds-of-list2-list
            (%cdr-cdr-induction x y))

(%ensure-exactly-these-rules-are-missing "../../utilities/tuple-listp")

