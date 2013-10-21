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

(defun kwote-list (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (cons (kwote (car x))
            (kwote-list (cdr x)))
    nil))

(mutual-recursion
 (defun add-tracing (term)
   (declare (xargs :mode :program))
   (cond ((variablep term)
          term)
         ((fquotep term)
          term)
         ((not (consp term))
          term)
         (t
          (let* ((fn (ffn-symb term))
                 (args (fargs term))
                 (traced-args (add-tracing-list args)))
            `(prog2$ (cw "~x0 ==> ~x1~%"
                         ',term
                         ,(cons fn traced-args))
                     ,term)))))
 (defun add-tracing-list (term-list)
   (declare (xargs :mode :program))
   (if (consp term-list)
       (cons (add-tracing (car term-list))
             (add-tracing-list (cdr term-list)))
     nil)))

(defun debug-guards-fn (term world)
  (declare (xargs :mode :program))
  (let* ((fn                (car term))
         (actuals           (kwote-list (cdr term)))
         (formals           (formals fn world))
         (guard             (guard fn nil world))
         (sigma             (pairlis$ formals actuals))
         (guard-sub         (sublis-expr sigma guard))
         (guard-sub-untrans (untranslate guard-sub nil world)))
    (add-tracing guard-sub-untrans)))

(defmacro debug-guards (form)
  ":Doc-Section Miscellaneous

  identify the cause of a guard violation. ~/

  If a function has an elaborate guard, it may be difficult to tell which
  part of the guard is being violated when a guard violation occurs.  The
  ~c[debug-guards] function may be useful in identifying the problem. ~/

  Below is a trivial example.  We define a function with several inputs
  and require that each input be a natural.

  ~bv[]
    ACL2 !> (defun f (a b c d e)
              (declare (xargs :guard (and (natp a)
                                          (natp b)
                                          (natp c)
                                          (natp d)
                                          (natp e))))
              (list a b c d e))
  ~ev[]

  We can now use debug-guards to see what would happen when we try to
  run this function on various arguments.  For example, perhaps we do
  not realize that the symbol d is not a natural.  Then, debug-guards
  will show us why this function call will fail:

  ~bv[]
    ACL2 !> (debug-guards '(f 1 2 3 d 5))
    (NATP 1) ==> T
    (NATP 2) ==> T
    (NATP 3) ==> T
    (NATP 'D) ==> NIL
    (AND (NATP 1) (NATP 2) (NATP 3) (NATP 'D) (NATP 5)) ==> NIL
  ~ev[]

  The argument to debug-guards should be a quoted function call, but
  you can also perform evaluation ahead of time, e.g., using ~c[list]
  as follows:

  ~bv[]
    ACL2 !> (defconst *d* 'd)

    ACL2 !> (debug-guards (list 'f 1 2 3 *d* 5))
    (NATP 1) ==> T
    (NATP 2) ==> T
    (NATP 3) ==> T
    (NATP 'D) ==> NIL
    (AND (NATP 1) (NATP 2) (NATP 3) (NATP 'D) (NATP 5)) ==> NIL
  ~ev[]
  ~/"
  `(let ((dbg-form (debug-guards-fn ,form (w state))))
     (er-progn (trans-eval dbg-form 'debug-guards state)
	       (value :invisible))))
