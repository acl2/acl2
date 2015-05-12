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

; pretty-defs-aux.lisp - Helper file for pretty-defs.lisp and pretty-defs-program.lisp.

(in-package "STR")

(defconst *pretty-defs*
  '(raise
    std::tuplep
    std::da-alist-name
    std::da-make-maker-fn-aux
    std::da-changer-args-to-alist
    std::extract-keywords
    std::da-patbind-make-field-acc-alist
    std::da-patbind-find-used-vars
    std::da-patbind-alist-to-bindings
    std::da-patbind-fn
    fty::patbind-flexsum
    fty::flexsum-p
    fty::flexsum->kind
    fty::flexsum->case
    fty::flexsum->prods
    fty::flexprod-p
    fty::flexprod->kind
    fty::flexprod->cond
    fty::flexprods->kinds
    fty::patbind-flexprod
    fty::flexprod->ctor-name
    fty::nice-cond
    fty::find-prod-by-kind
    fty::flexsum-case-macro-kinds
    fty::flexsum-case-macro-conds
    fty::flexsum-case-macro-member-special-form-expand
    fty::flexsum-case-macro-fn
    print-base-fix
    print-base-equiv
    acl2::pos-fix
    acl2::bool-fix
    acl2::symbol-fix
    printconfig-p
    printconfig
    printconfig->flat-right-margin
    printconfig->hard-right-margin
    printconfig->print-base
    printconfig->print-radix
    printconfig->home-package
    printconfig->print-lowercase
    make-printconfig-fn
    make-printconfig
    change-printconfig-fn
    change-printconfig
    patbind-printconfig
    *default-printconfig*
    basic-print-nat
    basic-print-int
    basic-print-rat
    basic-print-complex
    radix-print-int
    radix-print-rat
    radix-print-complex
    print-atom-aux
    print-atom
    print-escaped-charlist
    print-escaped-str-aux
    print-escaped-str
    my-needs-slashes
    in-home-package-p
    print-escaped-symbol
    print-escaped-atom
    nat-size
    int-size
    atom-size
    evisceratedp
    eviscerated->guts
    obj-size
    keyword-fix
    keyword-equiv

    pflat-p
    pflat
    pflat-fix
    pflat->width
    pflat->what
    make-pflat-fn
    make-pflat
    change-pflat-fn
    change-pflat
    patbind-pflat

    pinst-p
    pinst-kind
    pinst-case
    pinst-fix
    pinst-equiv

    pinst-flat
    pinst-flat->guts
    make-pinst-flat-fn
    make-pinst-flat
    patbind-pinst-flat

    pinst-dot
    pinst-dot->width
    make-pinst-dot-fn
    make-pinst-dot
    patbind-pinst-dot

    pinst-quote
    pinst-quote->width
    pinst-quote->guts
    make-pinst-quote-fn
    make-pinst-quote
    patbind-pinst-quote

    pinst-wide
    pinst-wide->width
    pinst-wide->first
    pinst-wide->rest
    make-pinst-wide-fn
    make-pinst-wide
    patbind-pinst-wide

    pinst-keyline
    pinst-keyline->guts
    make-pinst-keyline-fn
    make-pinst-keyline
    patbind-pinst-keyline

    pinst-keypair
    pinst-keypair->width
    pinst-keypair->kwd
    pinst-keypair->value
    make-pinst-keypair-fn
    make-pinst-keypair
    patbind-pinst-keypair

    pinst-indent
    pinst-indent->amount
    pinst-indent->width
    pinst-indent->first
    pinst-indent->rest
    make-pinst-indent-fn
    make-pinst-indent
    patbind-pinst-indent

    pinst->width
    pinstlist->max-width
    pprdot

    print-flat
    print-flat-objs
    spaces1
    spaces

    print-column
    keyword-param-valuep
    maybe-merge-flat
    cons-ppr1

    ppr1
    ppr
    pretty
    revappend-pretty
    pretty-list))
