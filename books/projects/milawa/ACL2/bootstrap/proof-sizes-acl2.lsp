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

; INSTRUCTIONS:
;
; After generating all the proofs and whatnot, run the following commands.
;
;   cd $(MILAWA)/Sources/ACL2/bootstrap
;   ./level2/symmetry < proof-sizes-acl2.lsp
;
; This generates the proof-sizes-acl2 executable, which can then be used
; to run the proof-sizes.lsp script.


; What does this script do?
;
; To compare the sizes of proofs at different levels, we want to be able
; to recreate the "environment" in which the proof was carried out.  That
; is, we want to store things such as the world and definitions that were
; in play at the time the proof was done.
;
; In this script, we begin by redefining %autoprove so that it will store
; the world which was being used at the beginning of each proof.  We then
; load all of the bootstrapping files where proofs are carried out.
;
; It takes several minutes to load all of the proofs.  Because of this, we want
; to go ahead and save a proof-sizes-acl2 executable, which we can use to carry
; out the re-proving, without having to reload all of these books.

(ACL2::set-ld-redefinition-action '(:warn . :overwrite) ACL2::state)

(ACL2::table proof-sizes 'autoprove-hints nil)

(defun get-autoprove-hints (world)
  (declare (xargs :mode :program))
  (cdr (lookup 'autoprove-hints (ACL2::table-alist 'proof-sizes world))))

(defmacro %autoprove (name &rest hints)
  `(ACL2::progn
    (ACL2::table proof-sizes 'autoprove-hints
                 (cons (let ((world (tactic.harness->world ACL2::world)))
                         (list ',name ',hints world))
                       (get-autoprove-hints ACL2::world)))
    (ACL2::make-event (autoprove-fn ',name ',hints ACL2::state))))



; These include-books grab everything EXCEPT the actual transitions to new
; proof checkers.  You MUST NOT include books such as level2/level2, or
; level3/level3, because they include %switch-builder calls which are
; irrevocable.  We do not want to switch the builders until we are ready to try
; the proof at different levels.

; Often the -acl2 book includes the supporting books.  I'm actually wanting to
; move away from that style.  To see what books you need to load, look at
; levelN.lisp, and see what it includes.  Then load all those books (not LevelN
; itself, just what it includes) and also load the -acl2 book.

(include-book "level2/support-3")
(include-book "level2/level2-acl2")  ;; doesn't include sub-books

(include-book "level3/prop")
(include-book "level3/pequal")
(include-book "level3/equal")
(include-book "level3/iff")
(include-book "level3/if")
(include-book "level3/not")
(include-book "level3/disjoined-update-clause-bldr")
(include-book "level3/level3-acl2") ;; doesn't include sub-books

(include-book "level4/level4-acl2")

(include-book "level5/level5-acl2")

(include-book "level6/level6-acl2")

(include-book "level7/level7-acl2")

(include-book "level8/level8-acl2")

(include-book "level9/world-check")
(include-book "level9/ancestors")
(include-book "level9/cachep")
(include-book "level9/fast-cache")
(include-book "level9/match-free")
(include-book "level9/rewrite-world-bldrs")
(include-book "level9/level9-acl2") ; doesn't include sub-books

(include-book "level10/crewrite-world")
(include-book "level10/level10-acl2") ; doesn't include sub-books

(include-book "level11/compiler")
(include-book "level11/level11-acl2") ; doesn't include sub-books


; Now that all the books are loaded, we can save our image.

:q

(ACL2::save-exec "proof-sizes-acl2" "Ready to compare proof sizes.")

