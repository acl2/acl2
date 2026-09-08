; The JVM package
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFPKG "JVM"
  (set-difference-equal
   (union-eq '(array-length ; remove?
               ;;record ops:
               s g
               ;; assoc-equal len nth zp syntaxp quotep fix nfix e0-ordinalp e0-ord-<
               defforall
               defforall-simple
               addressfix ; remove?
               addressp ; remove?
               null-refp ; remove?
               empty-map
               empty-list
               myif
               farg1 farg2 farg3 farg4 farg5
               lookup
               memberp
               lookup-eq
               lookup-equal
               ;; BV operators:
               bvchop
               bvsx
               bvand
               bvor
               bvxor
               bvshr
               bvashr
               bvshl
               bvplus
               bvminus
               bvuminus
               bvmult
               slice)
             (union-eq *acl2-exports*
                       (set-difference-eq nil ;*common-lisp-symbols-from-main-lisp-package* ;this is a lot of stuff...
                                          '(floatp typep))))
   ;; Symbols for which we do not want existing the ACL2 definitions:
   '(PC ; print a command
     PROGRAM ; turns on :program mode
     ;; PUSH POP RETURN
     REVERSE ; why?
     ;;STEP ++
     )))
