; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

; defs-aux.lisp - Helper file for defs.lisp and defs-program.lisp.

(in-package "STR")

(defconst *str-library-basic-defs*
  '(acl2::rest-n
    acl2::repeat
    repeat
    replicate
    prefixp
    listpos
    acl2::revappend-without-guard
    sublistp
    rev
    ;; coerce.lisp
    explode
    implode
    ;; Including this type-prescription rule improves the type-prescriptions of
    ;; some subsequent functions such as upcase-string.
    acl2::stringp-of-implode
    acl2::pos-fix

    ;; eqv.lisp
    character-list-fix
    charlisteqv
    charlisteqv-is-an-equivalence

    ;; cat.lisp
    ;; fast-string-append
    ;; fast-string-append-lst
    fast-concatenate
    cat
    append-chars-aux
    append-chars
    revappend-chars-aux
    revappend-chars
    prefix-strings
    ;; rchars-to-string
    join-aux
    join

    ;; char-case.lisp
    little-a
    little-z
    big-a
    big-z
    case-delta
    up-alpha-p
    down-alpha-p
    upcase-char
    downcase-char
    make-upcase-first-strtbl
    *upcase-first-strtbl*
    upcase-char-str
    make-downcase-first-strtbl
    *downcase-first-strtbl*
    downcase-char-str

    ;; case-conversion.lisp
    charlist-has-some-down-alpha-p
    upcase-charlist-aux
    upcase-charlist
    charlist-has-some-up-alpha-p
    downcase-charlist-aux
    downcase-charlist
    string-has-some-down-alpha-p
    upcase-string-aux
    upcase-string
    string-has-some-up-alpha-p
    downcase-string-aux
    downcase-string
    upcase-string-list-aux
    upcase-string-list
    downcase-string-list-aux
    downcase-string-list
    upcase-first-charlist
    upcase-first
    downcase-first-charlist
    downcase-first

    ;; ieqv.lisp
    ichareqv
    ichareqv-is-an-equivalence
    icharlisteqv
    icharlisteqv-is-an-equivalence
    istreqv-aux
    istreqv
    istreqv-is-an-equivalence

    ;; decimal.lisp
    dec-digit-char-p
    nonzero-dec-digit-char-p
    dec-digit-char-value
    dec-digit-char-listp
    dec-digit-chars-value1
    dec-digit-chars-value
    skip-leading-digits
    take-leading-dec-digit-chars
    digit-string-p-aux
    digit-string-p
    basic-natchars
    natchars-aux
    natchars
    revappend-natchars-aux
    revappend-natchars
    natstr
    natstr-list
    intstr
    intstr-list
    natsize-slow
    natsize-fast
    natsize
    parse-nat-from-charlist
    parse-nat-from-string
    strval

    ;; binary.lisp
    bin-digit-char-p
    bin-digit-char-listp
    bin-digit-char-value
    bin-digit-chars-value1
    bin-digit-chars-value
    skip-leading-bit-digits
    take-leading-bin-digit-chars
    bit-digit-string-p-aux
    bit-digit-string-p
    basic-natchars2
    natchars2-aux
    natchars2
    revappend-natchars2-aux
    revappend-natchars2
    natstr2
    natstr2-list
    natsize2
    parse-bits-from-charlist
    parse-bits-from-string
    strval2

    ;; hex.lisp
    hex-digit-char-p
    hex-digit-char-listp
    hex-digit-char-value
    hex-digit-chars-value1
    hex-digit-chars-value
    skip-leading-hex-digits
    take-leading-hex-digit-chars
    hex-digit-string-p-aux
    hex-digit-string-p
    hex-digit-to-char
    basic-natchars16
    natchars16-aux
    natchars16
    revappend-natchars16-aux
    revappend-natchars16
    natstr16
    natstr16-list
    natsize16-aux
    natsize16
    parse-hex-from-charlist
    parse-hex-from-string
    strval16

    ;; octal
    oct-digit-char-p
    nonzero-oct-digit-char-p
    oct-digit-char-value
    oct-digit-char-listp
    oct-digit-chars-value1
    oct-digit-chars-value
    skip-leading-octal-digits
    take-leading-oct-digit-chars
    octal-digit-string-p-aux
    octal-digit-string-p
    octal-digit-to-char
    basic-natchars8
    natchars8-aux
    natchars8
    revappend-natchars8-aux
    revappend-natchars8
    natstr8
    natstr8-list
    natsize8-aux
    natsize8
    parse-octal-from-charlist
    parse-octal-from-string
    strval8

    ;; firstn-chars.lisp
    firstn-chars-aux
    firstn-chars
    append-firstn-chars

    ;; html-encode.lisp
    html-space
    html-newline
    html-less
    html-greater
    html-amp
    html-quote
    repeated-revappend
    distance-to-tab
    html-encode-next-col
    html-encode-push
    html-encode-chars-aux
    html-encode-string-aux
    html-encode-string

    ;; iless.lisp
    ichar<
    icharlist<
    istr<-aux
    istr<

    ;; iprefixp.lisp
    iprefixp

    ;; istrprefixp.lisp
    istrprefixp-impl
    istrprefixp

    ;; istrpos.lisp
    istrpos-impl
    istrpos

    ;; isubstrp.lisp
    isubstrp
    collect-strs-with-isubstr
    collect-syms-with-isubstr
    ;; isort.lisp
    acl2::mergesort-fixnum-threshold
    istr-list-p
    istr-merge
    istr-merge-tr
    istr-mergesort-fixnum
    istr-mergesort-integers
    istr-sort
    istrsort

    ;; pad.lisp
    rpadchars
    rpadstr
    lpadchars
    lpadstr
    trim-aux
    trim-bag
    trim

    ;; prefix-lines.lisp
    prefix-lines-aux
    prefix-lines

    ;; strline.lisp
    charpos-aux
    go-to-line
    strline
    strlines

    ;; strnatless.lisp
    parse-nat-from-charlist
    parse-nat-from-string
    charlistnat<
    strnat<-aux
    strnat<

    ;; strprefixp.lisp
    strprefixp-impl
    strprefixp

    ;; strpos.lisp
    strpos-fast
    strpos

    ;; strrpos.lisp
    strrpos-fast
    strrpos

    ;; strsplit.lisp
    split-list-1
    split-list*
    character-list-listp
    coerce-list-to-strings
    strsplit

    ;; strsubst.lisp
    strsubst-aux
    strsubst
    strsubst-list

    ;; strtok.lisp
    strtok-aux
    strtok

    ;; substrp
    substrp

    ;; strsuffixp
    strsuffixp

    ;; symbols
    symbol-list-names
    intern-list-fn
    intern-list

    ;; url-encode
    url-encode-char
    make-url-encode-array
    *url-encode-array*
    fast-url-encode-char
    url-encode-chars-aux
    url-encode-chars
    url-encode-string-aux
    url-encode-string

    strrange-equiv
    ))
