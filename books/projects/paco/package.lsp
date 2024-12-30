(defpkg "PACO"
  '(

; ACL2 primitives:

    ACL2-NUMBERP BAD-ATOM BAD-ATOM<=
    BINARY-* BINARY-+ UNARY-- UNARY-/ < CAR CDR
    CHAR-CODE CHARACTERP CODE-CHAR COMPLEX COMPLEX-RATIONALP COERCE
    CONS CONSP DENOMINATOR EQUAL IF IMAGPART INTEGERP
    INTERN-IN-PACKAGE-OF-SYMBOL NUMERATOR RATIONALP REALPART STRINGP
    SYMBOL-NAME SYMBOL-PACKAGE-NAME SYMBOLP NOT EQ LENGTH ATOM ACONS
    ENDP NULL = /= ZP ZIP NTH CHAR CONJUGATE
    STANDARD-CHAR-P STRING ALPHA-CHAR-P UPPER-CASE-P LOWER-CASE-P
    CHAR-UPCASE CHAR-DOWNCASE STRING-DOWNCASE STRING-UPCASE CHAR-EQUAL
    STRING-EQUAL KEYWORDP IDENTITY REVAPPEND
    REVERSE

; At one point I deleted from this list all the symbols that used
; EQLABLEP in their guards.  I was then going to do the same for all
; symbols that used EQ.  But then I realized that true-listp uses EQ.
; Deleting it would mean defining my own TRUE-LISTP-EQUAL which annoys
; me.  I've decided to live in an ACL2-like world: logically there is
; no distinction between EQ and EQUAL and guards exist but are largely
; ignored.

   EQL MEMBER ASSOC RASSOC REMOVE REMOVE-DUPLICATES POSITION
   SUBSTITUTE SUBSETP SUBLIS SUBST

; These were omitted from the Posse East list.

    floor ceiling truncate round mod rem evenp oddp zerop
    plusp minusp min max abs signum lognot expt binary-append

    nfix e0-ordinalp e0-ord-<

    CHAR< CHAR> CHAR<= CHAR>= STRING< STRING> STRING<=
    STRING>= ZPF INTEGER-LENGTH LOGNAND
    LOGORC1 LOGORC2 LOGANDC1 LOGANDC2 LOGNOR LOGTEST SUBSEQ BUTLAST
    ACL2-COUNT

; Primitives that must be in ACL2 to be recognized by the ACL2 rule
; builders.  These were omitted from the Posse East list.

    implies
    iff
    true-listp
    len
; From *expandable-boot-strap-non-rec-fns*:
    synp listp prog2$ force case-split

; Macros and constants that are imported into Paco so that they
; can be expanded into primitives:

    quote
    nil
    t
    lambda
    declare
    ignore
    xargs
    otherwise

    int=
    digit-char-p
    intern
    append
    concatenate
    first
    second
    third
    fourth
    fifth
    sixth
    seventh
    eighth
    ninth
    tenth
    rest
    list*
    the-fixnum
    make-list
    the-mv
    the2s
    i-limited
    gc$

    + * - / > >= <= 1- 1+
    logand
    logeqv
    logior
    logxor

    let
    let*
    list
    cond
    case
    caaaar caaadr caaar caadar caaddr caadr caar cadaar cadadr cadar caddar
    cadddr caddr cadr cdaaar cdaadr cdaar cdadar cdaddr cdadr cdar cddaar
    cddadr cddar cdddar cddddr cdddr cddr
    mv
    mv-let
    mv-nth

    and or
    &rest

    progn
    the
    integer

; System level functions so the user can build an ACL2 logical world.

    trace
    untrace
    lp
    *main-lisp-package-name*
    *common-lisp-symbols-from-main-lisp-package*
    *common-lisp-specials-and-constants*

    mutual-recursion
    defun
    defthm
    defconst
    defmacro
    deflabel
    in-package
    verify-guards
    in-theory
    disable
    enable

; These symbols are used in :do-not hints.  Paco translates those
; hints with ACL2's translation mechanism, so these symbols are
; expected.  Paco may not support all these processes, but detects the
; supported hint after translation.

    preprocess
    simplify
    eliminate-destructors
    fertilize
    generalize
    eliminate-irrelevance

    ld
    value
    include-book
    thm
    local
    encapsulate

; Used in the nume tracker

    wormhole
    wormhole-eval
    wormhole-input
    wormhole-status
    make-wormhole-status
    wormhole-data
    set-wormhole-data
    er-progn
    assign
    @
    cw
    msg

    ))
