; The AES package
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFPKG "AES"
  ;; note: does not include state:
  '(all-unsigned-byte-p
    bv-arrayp-list
    2d-bv-arrayp
    unsigned-byte-p
    firstn nthcdr subrange array-elem-2d
    bvchop bvxor bvshl getbit
    ld thm in-package defun defund defthm defthmd defmacro defconst
    declare xargs type implies if not and or
    cons list consp endp include-book
    t nil
    + binary-+ - binary-- * binary-* / unary-/
    < <= > >= =
    equal
    enable disable in-theory e/d
    natp integerp rationalp acl2-numberp true-listp
    car cdr len nth update-nth
    &rest xxxjoin
    integer-length
    cond null
    let let*
    zp nfix ifix fix
    mod floor expt
    skip-proofs
    append binary-append
    encapsulate local
    syntaxp quotep
    revappend
    member-equal member-eq member-eql
    bind-free
    progn
    mbt))
