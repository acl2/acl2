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

(in-package "ACL2")

;; We introduce a wrapper for ls so that we can inspect generated files.  We
;; need a ttag to call sys-call, but this should be a sound extension of ACL2
;; as it does not muck with any system internals.

(defttag ls)

(defun ls (filename)
  (declare (xargs :guard (stringp filename))
           (ignore filename))
  (cw "ls has not yet been redefined under the hood~%"))

(progn!
 (set-raw-mode t)

 (defun ls (filename)
   ;; I've complained before that ACL2's sys-call does not provide a standard
   ;; interface across Lisps, but it has not been standardized.  So, calling
   ;; ls, which ought to be a really simple thing, is not and is probably buggy
   ;; in some cases.  This sort of shit is really lame, and makes me want to
   ;; use a different language.  In the meantime, we have this hacky solution.
   #+gcl
   ;; GCL needs the filename to be quoted, or it won't handle filenames with
   ;; spaces correctly.
   (if (position #\" filename)
       (ACL2::cw "Sorry.  ACL2's sys-call is too broken to use \"ls\" on files~
                  whose names include quotes on GCL.~%")
     (sys-call "ls" (list "-lh" (concatenate 'string "\"" filename "\""))))
   #+allegro
   ;; Allegro is completely fucked.  Whether or not you quote the string, the
   ;; spaces within it will be interpreted as argument separators.  So, I don't
   ;; know of any way to actually say ls "hello world.txt" in allegro.
   (if (position #\Space filename)
       (ACL2::cw "Sorry.  ACL2's sys-call is too broken to use \"ls\" on files~
                  whose names include spaces on Allegro.~%")
     (sys-call "ls" (list "-lh" filename)))
   #+(or clisp cmu openmcl sbcl)
   ;; CLISP, CMU, SBCL, and OpenMCL do not want the filename to be quoted, and
   ;; I think their behavior is the most proper.  You seem to be able to put
   ;; most anything you want into filenames here.
   (prog2$
    ;; Often prevent horrible death on fork when too much memory is allocated
    (funcall (intern "GC" (find-package "CCL")))
    (sys-call "ls" (list "-lh" filename)))
   #-(or gcl allegro clisp cmu openmcl sbcl)
   (ACL2::cw "Sorry.  ACL2's sys-call is not standardized, and support for this~
             platform has not yet been implemented.")
   nil
   ))
