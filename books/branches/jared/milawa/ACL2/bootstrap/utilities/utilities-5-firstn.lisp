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
(include-book "utilities-4")
(%interactive)



(%autoadmit firstn)

(%autoprove firstn-of-zero
            (%restrict default firstn (equal n ''0)))

(%autoprove true-listp-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove consp-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (or (equal n 'n) (equal n ''1))))

(%autoprove firstn-under-iff
            (%restrict default firstn (equal n 'n)))

(%autoprove firstn-of-list-fix
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove firstn-of-len
            (%cdr-induction x)
            (%restrict default firstn (equal n '(+ '1 (len x2)))))

(%autoprove len-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (or (equal n 'n) (equal n ''1))))

(%autoprove firstn-of-too-many
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(defsection firstn-of-too-many-replacement
  ;; BOZO fix acl2 to limit this
  ;;        -- NO, wait! First check if we need to do that now that we
  ;;           have our cache working
  (%prove (%rule firstn-of-too-many-replacement
                 :hyps (list (%hyp (< (len x) n) :limit 1))
                 :lhs (firstn n x)
                 :rhs (list-fix x)))
  (%auto)
  (%qed)
  (%disable default firstn-of-too-many)
  (%enable default firstn-of-too-many-replacement))

(%autoprove firstn-of-app
            ;; BOZO check if we still need this disable with our cache
            (%autoinduct firstn)
            (%disable default len-when-tuplep trichotomy-of-< antisymmetry-of-<)
            (%restrict default firstn (equal n 'n)))

(%autoprove subsetp-of-firstn-when-in-range
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))
