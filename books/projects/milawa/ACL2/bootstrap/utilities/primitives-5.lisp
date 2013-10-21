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
(include-book "primitives-4")
(%interactive)


;; Subtraction.

(%autoprove natp-of-minus
            (%use (build.axiom (axiom-natp-of-minus))))

(%autoprove minus-under-iff
            (local (%disable default natp-of-minus [outside]natp-of-minus))
            (%use (%thm natp-of-minus)))

(%autoprove minus-when-not-less
            (%use (build.axiom (axiom-minus-when-subtrahend-as-large))))

(%autoprove minus-of-self)

(%autoprove minus-of-zero-left)

(%autoprove minus-cancels-summand-right
            (%use (build.axiom (axiom-minus-cancels-summand-right))))

(%autoprove minus-of-zero-right
            (%enable default nfix)
            (%disable default minus-cancels-summand-right [outside]minus-cancels-summand-right)
            (%use (%instance (%thm minus-cancels-summand-right) (a a) (b 0))))

(%autoprove minus-cancels-summand-left
            (%disable default commutativity-of-+ nfix)
            (%eqsubst 't (+ a b) (+ b a)))

(%autoprove |(< (- a b) c)| (%use (build.axiom (axiom-less-of-minus-left))))
(%autoprove |(< a (- b c))| (%use (build.axiom (axiom-less-of-minus-right))))
(%disable default |[OUTSIDE](< a (- b c))|) ;; interferes with constant gathering

(%autoprove |(+ a (- b c))| (%use (build.axiom (axiom-plus-of-minus-right))))
(%autoprove |(+ (- a b) c)|)

(%autoprove |(- a (- b c))| (%use (build.axiom (axiom-minus-of-minus-right))))
(%autoprove |(- (- a b) c)| (%use (build.axiom (axiom-minus-of-minus-left))))
(%disable default |[OUTSIDE](- (- a b) c)|) ;; interferes with constant gathering

(%autoprove |(= (- a b) c)| (%use (build.axiom (axiom-equal-of-minus-property))))
(%autoprove |(= c (- a b))|)

(%autoprove |(- (+ a b) (+ a c))|)
(%autoprove |(- (+ a b) (+ c a))|)
(%autoprove |(- (+ b a) (+ c a))|)
(%autoprove |(- (+ b a) (+ a c))|)

(%autoprove |(- (+ a b) (+ c d a))|)

(%autoprove |a < b --> a <= b-1|
            (%enable default nfix))

(%autoprove minus-when-zp-left-cheap)

(%autoprove minus-when-zp-right-cheap)

(%autoprove minus-of-nfix-left)

(%autoprove minus-of-nfix-right)




;; Constant Gathering.  We break our normal forms when we can put two constants
;; next to one another, since they can then be evaluated away to make progress.

(%autoprove gather-constants-from-less-of-plus)

(%autoprove gather-constants-from-less-of-plus-two)

(%autoprove gather-constants-from-less-of-plus-and-plus)

(%autoprove lemma-for-gather-constants-from-equal-of-plus-and-plus)

(%autoprove lemma2-for-gather-constants-from-equal-of-plus-and-plus
            (%enable default nfix)
            (%auto)
            (%use (%instance (%thm trichotomy-of-<) (a c1) (b c2))))

(%autoprove gather-constants-from-equal-of-plus-and-plus
            (%use (%instance (%thm lemma-for-gather-constants-from-equal-of-plus-and-plus)))
            (%use (%instance (%thm lemma2-for-gather-constants-from-equal-of-plus-and-plus)))
            (%split))

(%autoprove gather-constants-from-equal-of-plus
            (%enable default nfix))

(%autoprove gather-constants-from-minus-of-plus)

(%autoprove gather-constants-from-minus-of-plus-two)

(%autoprove gather-constants-from-minus-of-plus-and-plus)

