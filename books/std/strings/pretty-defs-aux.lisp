; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

; pretty-defs-aux.lisp - Helper file for pretty-defs.lisp and pretty-defs-program.lisp.

(in-package "STR")

(defconst *pretty-defs*
  '(raise
    std::tuplep
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
    fty::flexsum-case-macro-kinds
    fty::flexsum-case-macro-conds
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
    change-printconfig-fn
    make-printconfig
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
    make-pinst-flat
    patbind-pinst-flat

    pinst-dot
    pinst-dot->width
    make-pinst-dot
    patbind-pinst-dot

    pinst-quote
    pinst-quote->width
    pinst-quote->guts
    make-pinst-quote
    patbind-pinst-quote

    pinst-wide
    pinst-wide->width
    pinst-wide->first
    pinst-wide->rest
    make-pinst-wide
    patbind-pinst-wide

    pinst-keyline
    pinst-keyline->guts
    make-pinst-keyline
    patbind-pinst-keyline

    pinst-keypair
    pinst-keypair->width
    pinst-keypair->kwd
    pinst-keypair->value
    make-pinst-keypair
    patbind-pinst-keypair

    pinst-indent
    pinst-indent->amount
    pinst-indent->width
    pinst-indent->first
    pinst-indent->rest
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
    revappend-pretty))
