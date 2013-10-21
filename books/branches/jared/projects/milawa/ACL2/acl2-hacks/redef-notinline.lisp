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
(include-book "defun" :ttags :all)

;; We introduce some macros which can be used to redefine functions in certain
;; ways that improve their traceability.
;;
;; IMPORTANT NOTE:  These macros only work on functions which
;;   (1) have their guards verified, and
;;   (2) were introduced with MILAWA::defun
;;
;; (redef-notinline foo)
;;   Redefines foo (with its own definition), but adds (declare (notinline foo))
;;   so that the compiler cannot optimize away recursive calls.  In some lisps,
;;   particularly OpenMCL, this will allow you to see all the calls with trace.
;;
;; (redef-original foo)
;;   Redefines foo with its own definition, and without adding the notinline
;;   declaration.  In other words, this "restores foo to its original version"
;;   which may give you better performance if the compiler chooses to optimize
;;   away recursive calls of foo.
;;
;;
;; Here is an example:
;;
;; ACL2 !> (in-package "ACL2")
;; ACL2 !> (MILAWA::defun fact (x acc)
;;           (declare (xargs :guard (and (natp x)
;;                                       (natp acc))))
;;           (if (zp x)
;;               acc
;;             (fact (- x 1) (* x acc))))
;; ACL2 !> (trace$ fact)
;; ACL2 !> (fact 5 1)
;;
;; 1> (ACL2_*1*_ACL2::FACT 5 1)
;;   2> (FACT 5 1)
;;   <2 (FACT 120)
;; <1 (ACL2_*1*_ACL2::FACT 120)
;; 120
;;
;; ACL2 !> (redef-notinline fact)
;; ACL2 !> (fact 5 1)
;;
;; 1> (ACL2_*1*_ACL2::FACT 5 1)
;;   2> (FACT 5 1)
;;     3> (FACT 4 5)
;;       4> (FACT 3 20)
;;         5> (FACT 2 60)
;;           6> (FACT 1 120)
;;             7> (FACT 0 120)
;;             <7 (FACT 120)
;;           <6 (FACT 120)
;;         <5 (FACT 120)
;;       <4 (FACT 120)
;;     <3 (FACT 120)
;;   <2 (FACT 120)
;; <1 (ACL2_*1*_ACL2::FACT 120)
;; 120
;;
;; ACL2 !> (redef-original fact)
;; ACL2 !> (fact 5 1)
;;
;; 1> (ACL2_*1*_ACL2::FACT 5 1)
;;   2> (FACT 5 1)
;;   <2 (FACT 120)
;; <1 (ACL2_*1*_ACL2::FACT 120)
;; 120

(defun redef-notinline-fn (f notinlinep)
   (declare (ignore f notinlinep)
            (xargs :guard t))
   nil)

(defttag redef-notinline)

(progn!
 (set-raw-mode t)
 (defun redef-notinline-fn (f notinlinep)
   (let* ((state *the-live-state*)
          (world   (w state))
          (def     (assoc f (get-acl2-defun-entries world))))
     (if (not def)
         (cw "redef-notinline-fn: attempting to redefine ~x0, which wasn't introduced with MILAWA::defun.~%" f)
       (let* ((formals (second def))
              (new-def (if notinlinep
                           `(defun ,f ,formals
                              ,@(cons `(declare (notinline ,f)) (cddr def)))
                         `(defun ,f ,formals
                            ,@(cddr def)))))
         (eval new-def)
         nil)))))

(defmacro redef-original (f)
  `(redef-notinline-fn ',f nil))

(defmacro redef-notinline (f)
  `(redef-notinline-fn ',f t))



