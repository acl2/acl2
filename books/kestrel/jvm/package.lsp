; The JVM package
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFPKG "JVM"
  (set-difference-equal
   (union-eq '(array-length
               ;;record ops:
               acl2::s acl2::g
               ASSOC-EQUAL LEN NTH ZP SYNTAXP
               QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<
               acl2::defforall
               acl2::defforall-simple
               acl2::addressfix
               acl2::addressp
               acl2::null-refp
               acl2::empty-map
               acl2::empty-list
               myif
               farg1 farg2 farg3 farg4 farg5
               lookup
               memberp
               )
             (union-eq *acl2-exports*
                       (set-difference-eq nil ;*common-lisp-symbols-from-main-lisp-package* ;this is a lot of stuff...
                                          '(floatp typep))))
   ;;stuff to subtract out:
   '(PC PROGRAM PUSH POP RETURN REVERSE STEP ++)))
