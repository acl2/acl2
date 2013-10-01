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

;; car-cdr-untranslate.lisp
;;
;; This file just sets up some "untranslate patterns" which trick ACL2 into
;; printing (second x), (third x), (fourth x), etc., instead of (cadr x),
;; (caddr x), and (cadddr x) during proof attempts.  This yields much more
;; readable output, in my opinion.
;;
;; BOZO I thought about submitting this book to the ACL2 distribution as a
;; "misc" book, but even if we do that we won't be able to just include it
;; because we need to use MILAWA::first instead of ACL2::first, etc.

(in-package "MILAWA")

(include-book "misc/untranslate-patterns" :dir :system)

(ACL2::add-untranslate-pattern (car ?x)
                               (first ?x))

(ACL2::add-untranslate-pattern (car (car ?x))
                               (first (first ?x)))

(ACL2::add-untranslate-pattern (car (cdr ?x))
                               (second ?x))

(ACL2::add-untranslate-pattern (car (car (cdr ?x)))
                               (first (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car (cdr ?x))))
                               (second (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car ?x)))
                               (second (first ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr ?x)))
                               (third ?x))

(ACL2::add-untranslate-pattern (car (car (cdr (cdr ?x))))
                               (first (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car (cdr (cdr ?x)))))
                               (second (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr ?x))))))
                               (second (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr ?x)))))
                               (third (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car ?x))))
                               (third (first ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr ?x))))
                               (fourth ?x))

(ACL2::add-untranslate-pattern (car (car (cdr (cdr (cdr ?x)))))
                               (first (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car (cdr (cdr (cdr ?x))))))
                               (second (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr (cdr ?x)))))))
                               (third (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr (cdr ?x))))))))
                               (fourth (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr ?x)))))))
                               (fourth (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr ?x))))))
                               (fourth (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car ?x)))))
                               (fourth (first ?x)))

(ACL2::add-untranslate-pattern (first (cdr ?x))
                               (second ?x))

(ACL2::add-untranslate-pattern (first (cdr (cdr ?x)))
                               (third ?x))

(ACL2::add-untranslate-pattern (first (cdr (cdr (cdr ?x))))
                               (fourth ?x))

(ACL2::optimize-untranslate-patterns)