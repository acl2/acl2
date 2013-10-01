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

; pcert.lisp -- provisional certification mechanism

(in-package "ACL2")



;; We implement our own provisional certification scheme for bootstrapping.
;; This predates ACL2's notion of provisional certificates.  We might
;; eventually switch to ACL2's new pcert mechanism, but at present it is not
;; very mature and our scheme doesn't require the extra acl2x pass.
;;
;; Basic instructions for using this scheme:
;;
;;   (provisionally-certify "foo")
;;
;; This is ordinarily done by the pcert.pl script.
;;
;; For earlier versions of ACL2 (up through at least 4.1) the certify-book-info
;; state global was just a string naming the book, and I did something here to
;; emulate certify-book.  But with the new ACL2 pcert mechanism, this is now
;; some complicated stupid defrec with very complicated semantics.  I don't
;; know how to properly fake it, and keep hitting problems with uncertified-okp
;; not being allowed no matter what mode I try.  Worse, I suspect this is all
;; going to get overhauled again soon and so I'll have to update whatever I do
;; to solve it.
;;
;; Well, fortunately the only function I was taking advantage of this was the
;; current-book-info macro from acl2-hacks/io.lisp, and it seems that this
;; macro was not even being used at all, so it doesn't really matter.
;;
;; So, now our pcert mechanism involves very little.  We basically just try to
;; ld the file, and see if it was successful.  If we successfully load the
;; file, we write out a .pcert file with its checksum.

(defun check-sum-file (filename state)
  (declare (xargs :guard (stringp filename) :mode :program :stobjs state))
  (mv-let (channel state)
          (open-input-channel filename :object state)
          (mv-let (sum state)
                  (check-sum channel state)
                  (let ((state (close-input-channel channel state)))
                    (mv sum state)))))

;; This is very basic.  It doesn't do any embeddable event checks
;; but does fail for incorrect theorems, at least.

(defun provisionally-certify-fn (filename state)
  (declare (xargs :guard (stringp filename)
                  :mode :program
                  :stobjs state))
  (let ((lisp-file  (concatenate 'string filename ".lisp"))
        (pcert-file (concatenate 'string filename ".mpcert")))
    (ld `((cw "Provisionally certifying ~x0.~%" ,filename)
          (ld ,lisp-file :ld-error-action :error)
          (mv-let (channel state) (open-output-channel ,pcert-file :object state)
            (mv-let (sum state) (check-sum-file ,lisp-file state)
              (let* ((state (fms! "~f0 check-sum ~f1~|"
                                  (list (cons #\0 ,lisp-file)
                                        (cons #\1 sum))
                                  channel state nil)))
                (close-output-channel channel state))))
          (cw "Provisional certification successful.~%")
          (exit 44)))))

(defmacro provisionally-certify (filename)
  `(provisionally-certify-fn ,filename state))

