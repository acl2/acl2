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
(include-book "fast-image")


(%autoprove rw.ftrace->rhs-of-rw.fast-crewrite-core
            (%disable default rw.trace-fast-image-of-rw.crewrite-core)
            (%use (%instance (%thm rw.trace-fast-image-of-rw.crewrite-core))))


#||

;; this shoudln't be needed anymore

(%autoadmit rw.aux-fast-crewrite)

(%autoprove rw.ftracep-of-rw.aux-fast-crewrite
            (%autoinduct rw.aux-fast-crewrite)
            (%restrict default rw.aux-fast-crewrite (equal n 'n)))

(%autoprove rw.trace-fast-image-of-rw.aux-crewrite
            (%autoinduct rw.aux-crewrite)
            (%restrict default rw.aux-crewrite (equal n 'n))
            (%restrict default rw.aux-fast-crewrite (equal n 'n)))

||#

(%autoadmit rw.fast-crewrite)

(%autoprove rw.ftracep-of-rw.fast-crewrite
            (%enable default rw.fast-crewrite))

(%autoprove rw.trace-fast-image-of-rw.crewrite
            (%enable default rw.crewrite rw.fast-crewrite))

(%autoprove rw.ftrace->rhs-of-rw.fast-crewrite
            (%disable default rw.trace-fast-image-of-rw.crewrite)
            (%use (%instance (%thm rw.trace-fast-image-of-rw.crewrite))))

(%autoprove rw.ftrace->fgoals-of-rw.fast-crewrite
            (%disable default rw.trace-fast-image-of-rw.crewrite)
            (%use (%instance (%thm rw.trace-fast-image-of-rw.crewrite))))
