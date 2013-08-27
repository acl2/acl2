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
(include-book "base")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defsection iabs

  (defund iabs (a)
    (declare (xargs :guard t))
    (if (i< a 0)
        (ineg a)
      (ifix a)))

  (local (in-theory (enable integerp iabs ifix ineg i<)))

  (defthm natp-of-iabs
    (equal (natp (iabs a))
           t))

  (defthm iabs-of-ifix
    (equal (iabs (ifix a))
           (iabs a)))

  (defund fast-iabs (a)
    (declare (xargs :guard (integerp a)))
    (if (consp a)
        (cdr a)
      a))

  (defthm fast-iabs-removal
    (implies (force (integerp a))
             (equal (fast-iabs a)
                    (iabs a)))
    :hints(("Goal" :in-theory (enable fast-iabs)))))



(defsection imax

  (defund imax (a b)
    (declare (xargs :guard t))
    (if (i< a b)
        (ifix b)
      (ifix a)))

  (local (in-theory (enable imax)))

  (defthm integerp-of-imax
    (equal (integerp (imax a b))
           t))

  (defthm imax-of-ifix-left
    (equal (imax (ifix a) b)
           (imax a b)))

  (defthm imax-of-ifix-right
    (equal (imax a (ifix b))
           (imax a b)))

  (defthm |(i< (imax a b) a)|
    (equal (i< (imax a b) a)
           nil))

  (defthm |(i< (imax a b) b)|
    (equal (i< (imax a b) b)
           nil))

  (defund fast-imax (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (if (fast-i< a b)
        b
      a))

  (defthm fast-imax-removal
    (implies (force (and (integerp a)
                         (integerp b)))
             (equal (fast-imax a b)
                    (imax a b)))
    :hints(("Goal" :in-theory (enable fast-imax)))))



(defsection imin

  (defund imin (a b)
    (declare (xargs :guard t))
    (if (i< a b)
        (ifix a)
      (ifix b)))

  (local (in-theory (enable imin)))

  (defthm integerp-of-imin
    (equal (integerp (imin a b))
           t))

  (defthm imin-of-ifix-left
    (equal (imin (ifix a) b)
           (imin a b)))

  (defthm imin-of-ifix-right
    (equal (imin a (ifix b))
           (imin a b)))

  (defthm |(i< a (imin a b))|
    (equal (i< a (imin a b))
           nil))

  (defthm |(i< b (imin a b))|
    (equal (i< b (imin a b))
           nil))

  (defund fast-imin (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (if (fast-i< a b)
        a
      b))

  (defthm fast-imin-removal
    (implies (force (and (integerp a)
                         (integerp b)))
             (equal (fast-imin a b)
                    (imin a b)))
    :hints(("Goal" :in-theory (enable fast-imin)))))

