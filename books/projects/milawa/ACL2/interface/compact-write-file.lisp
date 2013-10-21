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
(include-book "misc/hons-help2" :dir :system)
(include-book "compact-print")

;; This is the same as ACL2's compact-write-file, except that it prints symbols
;; from the MILAWA package instead of the ACL2 package.  This helps keep file
;; sizes down, e.g., we only print PEQUAL* instead of MILAWA::PEQUAL*, etc.
;;
;; Though we use a ttag, this should be a sound extension of ACL2 as it does
;; not muck with any system internals.

(defund MILAWA::compact-write-file (data filename)
  (declare (xargs :guard t)
           (ignore data))
  (progn$
   (cw "Warning: compact-write-file has not been redefined!~%")
   filename))

(defttag compact-write-file)

(progn!
 (set-raw-mode t)
 (defund MILAWA::compact-write-file (data filename)
   (setq *compact-print-file-ht* (hl-mht))
   (setq *compact-print-file-n* 0)
   (setq *space-owed* nil)
   (with-open-file (*standard-output* filename
                                      :direction :output
                                      :if-does-not-exist :create
                                      :if-exists :supersede)
                   (with-standard-io-syntax
                    (let ((*package* (find-package "MILAWA"))
                          (*readtable* *acl2-readtable*))
                      (compact-print-file-scan data)
                      (compact-print-file-help data
                                               (gethash data *compact-print-file-ht*)
                                               ;; In V3-5, an extra stream argument was added.  We still
                                               ;; want to support v3-4, so we only sometimes add the arg.
                                               #-v3-4 *standard-output*
                                               )
                      (setq *compact-print-file-ht* (hl-mht)))))
   filename))

(value-triple (milawa::compact-write-file '(1 . 2) "compact-write-file.test.out"))