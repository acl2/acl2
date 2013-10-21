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
(%interactive)


(include-book
 ;; Fooling dependency scanner with newline because of provisional
 ;; certification problems with loading other books.  Generally we certify all
 ;; ACL2 books before doing the Milawa translation, so this isn't a problem.
 ;; Bug Jared to fix omake stuff if you need this to work.
 "../../utilities/arithmetic/multiply")



;; This file gives a demo of using our highest-level proof checker.
;;
;; This is probably completely stupid, since there are 13 other directories
;; filled with examples of proofs, and the particular proof-checker being
;; used is utterly irrelevant except for proof sizes.
;;
;; On the other hand, at least we get to test that our interface is
;; creating proofs that are accepted by level11.proofp.
;;
;; What shall we prove?  Well, multiplication is not one of our primitives.
;; Nor, in fact, is it used anywhere in Milawa.  But once upon a time, I looked
;; at writing a more complete library for basic arithmetic, so if you look in
;; Sources/ACL2/utilities/arithmetic you will find some various lemmas about
;; multiplication, division, and so on.  In particular, to see what theorems
;; we are proving, see
;;
;;    Sources/ACL2/utilities/arithmetic/multiply.lisp
;;
;; I imagined adding multiplication as a new primitive.  But for this simple
;; example file, I will just give it the recursive definition I had imagined
;; would be its defining axiom.  There's no ACL2 analogue, so we use %defun
;; explicitly.
;;
;; In every other file you'll see %autoadmit being used instead, except
;; probably for something like prepare-for-bootstrapping.lisp in the utilities
;; directory.  But if you look at the macros in the ACL2/interface directory,
;; you'll find that %defun and %admit can be used manually.  There are similar
;; facilities called %prove and %qed, instead of %autoprove.  If you are going
;; to use Milawa at all, you will probably need to read through the interface
;; files to see what commands are available.

(%building t) ;; Turn on proof building, for demo purposes
(%saving t)   ;; Turn on proof saving, for demo purposes
(%checking t) ;; Turn on proof checking, for demo purposes


;; Introduce multiply manually, since the ACL2 definition in
;; extended-primitives is "under the hood" and not legitimate.

(encapsulate
 ()
 (%defun * (a b)
         (if (zp a)
             0
           (+ b (* (- a 1) b)))
         :measure (nfix a))
 (%auto)
 (%admit))

(%autoprove natp-of-*
            (%restrict default * (equal a 'a)))

(%autoprove *-when-not-natp-left-cheap
            (%restrict default * (equal a 'a)))

(%autoprove *-when-not-natp-right-cheap
            (%dec-induction a)
            (%restrict default * (equal a 'a)))

(%autoprove *-when-zp-left-cheap
            (%restrict default * (equal a 'a)))

(%autoprove *-when-zp-right-cheap
            (%dec-induction a)
            (%restrict default * (equal a 'a)))

(%autoprove |(* 0 a)|
            (%restrict default * (equal a ''0)))

(%autoprove |(* a 0)|
            (%dec-induction a)
            (%restrict default * (equal a 'a)))

(%autoprove |(* (nfix a) b)|
            (%enable default nfix))

(%autoprove |(* a (nfix b))|
            (%enable default nfix))

(%autoprove |(* 1 a)|
            (%restrict default * (equal a ''1)))

(%autoprove |(* a 1)|
            (%dec-induction a)
            (%restrict default * (equal a 'a)))

(%autoprove |(equal (* a b) 0)|
            (%dec-induction a)
            (%restrict default * (equal a 'a)))

(%autoprove |(* (+ a c) b)|
            (%dec-induction a)
            (%restrict default *
                       (or (equal a '(+ '1 c))
                           (equal a '(+ a c))
                           (equal a 'a)
                           (equal a 'c))))

(%autoprove |(* a (+ b c))|
            (%dec-induction a)
            (%restrict default *
                       (and (equal a 'a)
                            (or (equal b 'b)
                                (equal b '(+ b c))
                                (equal b 'c)))))

(%autoprove |(* (- a b) c)|
            (%dec-dec-induction a b)
            (%restrict default *
                       (and (equal b 'c)
                            (or (equal a '(- a b))
                                (equal a '(- a '1))
                                (equal a 'a)
                                (equal a 'b)))))

(%autoprove |(* a (- b c))|
            (%dec-induction a)
            (%restrict default *
                       (and (equal a 'a)
                            (or (equal b 'b)
                                (equal b 'c)
                                (equal b '(- b c)))))
            (%disable default |(* (- a b) c)|))

(%autoprove |(< a (* a b))|
            (%dec-induction a))

(%autoprove |(< b (* a b))|
            (%dec-induction a)
            (%restrict default * (equal a 'a))
            (%disable default |(* (- a b) c)|))

(%autoprove |(< (* a b) a)|
            (%dec-induction a))

(%autoprove |(< (* a b) b)|
            (%dec-induction a))

(%autoprove |(< (* a c) (* b c))|
            (%dec-dec-induction a b))

(%autoprove |(< (* a b) (* a c))|
            (%dec-induction a))

(%autoprove associativity-of-*
            (%dec-induction a))

(%autoprove commutativity-of-*
            (%dec-induction a))

(%autoprove commutativity-of-*-two
            (%use (%instance (%thm commutativity-of-*)
                             (a a) (b (* b c)))))

(%autoprove |(= a (* a b))|
            (%restrict default *
                       (or (and (equal a 'a) (equal b 'b))
                           (and (equal a 'b) (equal b '(- a '1)))))
            (%disable default |(* a (- b c))|))

(%autoprove |(= 1 (* a b))|
            (%restrict default * (and (equal a 'a) (equal b 'b)))
            (%use (%instance (%thm |(* a (- b c))|)
                             (a b) (b a) (c 1)))
            (%disable default |(* a (- b c))|))


;; Keeping current with ACL2 file if any theorems are added:

(%ensure-exactly-these-rules-are-missing "../../utilities/arithmetic/multiply"
                                         ;; no rules are missing, but if we wanted
                                         ;; to exclude some, we'd list them here.
                                         )


;; When you're done with a bunch of files, you can save an events file like
;; this.  The %finish command inserts a finish command so that processing the
;; .events file gives you a new image with the events loaded.  You should also
;; clear out the thmfiles table any time you run save-events, so you don't
;; process the same events again later.  I typically do this once per
;; directory.

(%finish "user")
(%save-events "user.events")
(ACL2::table tactic-harness 'thmfiles nil)


