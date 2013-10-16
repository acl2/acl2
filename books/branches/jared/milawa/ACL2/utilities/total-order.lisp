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
(include-book "primitives")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund << (x y)
  ;; This is a total order over Milawa objects.
  ;;
  ;; We say naturals are smaller than symbols, which are smaller than conses,
  ;; which are recursively ordered lexiographically.  We include a special hack
  ;; for ACL2 compatibility to make this a total order on ACL2 objects as well.
  (declare (xargs :guard t
                  :export
                  ;; We export a Milawa definition that doesn't include the
                  ;; special case for ACL2 compatibility.
                  (cond ((natp x)
                         (if (natp y)
                             (< x y)
                           t))
                        ((natp y)
                         nil)
                        ((symbolp x)
                         (if (symbolp y)
                             (symbol-< x y)
                           t))
                        ((symbolp y)
                         nil)
                        (t
                         (if (equal (car x) (car y))
                             (<< (cdr x) (cdr y))
                           (<< (car x) (car y)))))))
  (cond ((natp x)
         (if (natp y)
             (< x y)
           t))
        ((natp y)
         nil)
        ((symbolp x)
         (if (symbolp y)
             (symbol-< x y)
           t))
        ((symbolp y)
         nil)
        ((or (not (consp x))
             (not (consp y)))
         ;; HACK: Special case for ACL2 compatibility.  We should not need
         ;; this case in Milawa.
         (if (consp x)
             nil
           (if (consp y)
               t
             (and (ACL2::lexorder x y)   ;; ACL2's usual total order
                  (not (equal x y))))))
        (t
         (if (equal (car x) (car y))
             (<< (cdr x) (cdr y))
           (<< (car x) (car y))))))

(local (defthm booleanp-of-acl2-lexorder
         (equal (booleanp (ACL2::lexorder x y))
                t)
         :hints(("Goal" :in-theory (enable booleanp)))))

(defthm booleanp-of-<<
  (equal (booleanp (<< x y))
         t)
  :hints(("Goal" :in-theory (enable <<))))

(defthm irreflexivity-of-<<
  (equal (<< x x)
         nil)
  :hints(("Goal" :in-theory (enable <<))))

(defthm asymmetry-of-<<
  (implies (<< x y)
           (equal (<< y x)
                  nil))
  :hints(("Goal" :in-theory (enable <<))))

(defthm transitivity-of-<<
  (implies (and (<< x y)
                (<< y z))
           (equal (<< x z)
                  t))
  :hints(("Goal" :in-theory (enable <<))))

(defthm forcing-trichotomy-of-<<
  (implies (and (not (<< x y))
                (not (equal x y)))
           (equal (<< y x)
                  t))
  :hints(("Goal" :in-theory (enable <<))))
