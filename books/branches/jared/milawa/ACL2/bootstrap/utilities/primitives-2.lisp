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
(include-book "primitives-1")
(%interactive)


;; BOZO reorganize these properly

(%autoprove natp-of-nfix
            (%enable default nfix))

(%autoprove nfix-when-natp-cheap
            (%enable default nfix))

(%autoprove nfix-when-not-natp-cheap
            (%enable default nfix))

(%autoprove equal-of-nfix-of-self)

(defsection [outside]equal-of-nfix-of-self-alt
  ;; Can't rely on term-order for outside-in.
  (%prove (%rule [outside]equal-of-nfix-of-self-alt
                 :type outside
                 :lhs (equal (nfix x) x)
                 :rhs (natp x)))
  (%auto)
  (%qed)
  (%enable default [outside]equal-of-nfix-of-self-alt))

(%autoprove equal-of-zero-and-nfix
            (%enable default nfix zp))

(defsection [outside]equal-of-zero-and-nfix-alt
  ;; Can't rely on term-order for outside-in.
  (%prove (%rule [outside]equal-of-zero-and-nfix-alt
                 :type outside
                 :lhs (equal (nfix x) 0)
                 :rhs (zp x)))
  (%auto)
  (%qed)
  (%enable default [outside]equal-of-zero-and-nfix-alt))

(%autoprove zp-when-natp-cheap
            (%enable default zp))

(%autoprove zp-when-not-natp-cheap
            (%enable default zp))

(%autoprove zp-of-nfix
            (%enable default nfix))

(%autoprove nfix-of-nfix)

(%autoprove natp-when-not-zp-cheap)

(%autoprove natp-when-zp-cheap)

(%autoprove nfix-when-zp-cheap)

(%autoprove equal-of-nfix-with-positive-constant
            (%enable default nfix))



;; Addition.

(%autoprove natp-of-plus
            (%use (build.axiom (axiom-natp-of-plus))))

(%autoprove plus-under-iff
            (%disable default natp-of-plus [outside]natp-of-plus)
            (%use (%thm natp-of-plus)))

(%autoprove commutativity-of-+
            (%use (build.axiom (axiom-commutativity-of-+))))

(%autoprove associativity-of-+
            (%use (build.axiom (axiom-associativity-of-+))))

(%disable default [outside]associativity-of-+) ;; Interferes with constant gathering

(%autoprove commutativity-of-+-two
            (%use (%instance (build.axiom (axiom-commutativity-of-+)) (b (+ b c)))))

(%autoprove gather-constants-from-plus-of-plus)



(%autoprove plus-completion-left
            (%use (build.axiom (axiom-plus-when-not-natp-left)))
            (%use (build.instantiation (build.axiom (axiom-plus-of-zero-when-natural))
                                       (list (cons 'a 'b))))
            (%use (build.axiom (axiom-plus-when-not-natp-left)))
            (%use (build.instantiation (build.axiom (axiom-plus-when-not-natp-left))
                                       (list (cons 'a 'b)
                                             (cons 'b ''0)))))

(%autoprove plus-completion-right
            (%disable default nfix plus-completion-left)
            (%use (%instance (%thm plus-completion-left) (a b) (b a))))

(%autoprove plus-of-zero-right
            (%enable default plus-completion-right)
            (%use (build.axiom (axiom-plus-of-zero-when-natural))))

(%autoprove plus-of-zero-left
            (%use (%instance (%thm commutativity-of-+) (a 0) (b a))))

(%autoprove plus-when-zp-left-cheap
            (%use (%thm plus-completion-left)))

(%autoprove plus-when-zp-right-cheap
            (%use (%thm plus-completion-right)))

(%autoprove plus-of-nfix-left
            (%enable default nfix))

(%autoprove plus-of-nfix-right
            (%enable default nfix))




;; Less-Than Relation.

(%autoprove booleanp-of-<
            (%use (build.axiom (axiom-<-nil-or-t))))

(%autoprove irreflexivity-of-<
            (%use (build.axiom (axiom-irreflexivity-of-<))))

(%autoprove less-of-zero-right
            (%use (build.axiom (axiom-less-of-zero-right))))

(%autoprove less-completion-right
            (%use (build.axiom (axiom-less-completion-right))))

(%autoprove less-when-zp-right-cheap
            (%use (%thm less-completion-right)))

(%autoprove less-of-zero-left
            (%use (build.axiom (axiom-less-of-zero-left-when-natp))))

(%autoprove less-completion-left
            (%use (build.axiom (axiom-less-completion-left))))

(%autoprove less-when-zp-left-cheap
            (%use (%thm less-completion-left)))

(%autoprove less-of-nfix-left
            (%enable default nfix))

(%autoprove less-of-nfix-right
            (%enable default nfix))

(%autoprove transitivity-of-<
            (%use (build.axiom (axiom-transitivity-of-<))))

(%autoprove antisymmetry-of-<
            (%disable default transitivity-of-<)
            (%use (%instance (%thm transitivity-of-<) (a a) (b b) (c a))))

(%autoprove trichotomy-of-<
            (%use (build.axiom (axiom-trichotomy-of-<-when-natp))))

(%autoprove one-plus-trick
            (%use (build.axiom (axiom-one-plus-trick))))

(%autoprove less-of-one-right
            (%use (build.axiom (axiom-natural-less-than-one-is-zero))))

(%autoprove less-of-one-left
            (%enable default zp))

(%autoprove transitivity-of-<-two
            (%enable default nfix)
            (%disable default trichotomy-of-<)
            (%use (%instance (%thm trichotomy-of-<) (a b) (b c))))

(%autoprove transitivity-of-<-three)

(%autoprove transitivity-of-<-four)


