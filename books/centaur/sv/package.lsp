; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(include-book "std/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "centaur/vl/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)

(defpkg "SV"
  (set-difference-eq
   (union-eq
    *standard-acl2-imports*
    std::*std-exports*
    set::*sets-exports*
    bitops::*bitops-exports*
    bitops::*sparseint-exports*
    ;; Things we want to "export"
    '()
    ;; Things we want to "import"
    '(assert!
      b*
      fun
      append-without-guard
      flatten
      strip-cadrs
      simpler-take
      repeat
      replicate
      list-fix
      true-list-fix
      true-list-listp
      true-list-list-fix
      true-list-list-equiv
      llist-fix
      list-equiv
      same-lengthp
      rev
      revappend-without-guard
      unexplode-nonnegative-integer
      base10-digit-char-listp
      prefixp
      set-equiv
      set-reasoning
      maybe-natp
      maybe-stringp
      maybe-posp
      maybe-integerp
      never-memoize

      std::mksym
      std::mksym-package-symbol
      std::extract-keyword-from-args
      std::throw-away-keyword-parts

      value
      file-measure
      two-nats-measure
      add-untranslate-pattern
      conjoin
      conjoin2
      disjoin
      disjoin2
      access
      rewrite-rule
      augment-theory
      find-rules-of-rune
      signed-byte-p
      unsigned-byte-p
      cwtime
      xf-cwtime
      defxdoc
      undocumented
      progn$

      make-fal
      make-fast-alist
      with-fast-alist
      with-fast
      with-stolen

      run-when
      run-if
      run-unless
      assocs

      defconsts
      definline
      definlined

      witness
      def-universal-equiv
      definstantiate
      defexample
      defwitness
      defquant

      seq
      seq-backtrack
      seqw
      seqw-backtrack
      cw-obj
      return-raw

      uniquep
      duplicity
      duplicated-members
      <<-sort
      hons-duplicated-members

      sneaky-load
      sneaky-push
      sneaky-save

      cw-unformatted

      alists-agree
      alist-keys
      alist-vals
      alist-equiv
      sub-alistp
      hons-rassoc-equal

      def-ruleset
      def-ruleset!
      add-to-ruleset
      add-to-ruleset!
      get-ruleset
      ruleset-theory
      enable*
      disable*
      e/d*
      e/d**

      make-fast-alist
      with-fast-alist
      with-fast
      with-fast-alists

      str::cat
      str::natstr
      str::implode
      str::explode

      ;; acl2-customization file stuff
      why
      with-redef

      f w x y z g s
      def-b*-binder
      std::defines
      std::defret
      mod
      index-of
      nat-list-measure
      fty::defprod
      fty::deflist
      fty::defalist
      fty::deftypes
      fty::deffixequiv
      fty::deffixequiv-mutual
      fty::deffixtype
      fty::defflexsum
      fty::deffixcong
      fty::fty-discipline

      natarr get-nat set-nat resize-nats
      u32arr u32s-length get-u32 set-u32 resize-u32s set-u32n

      aig-eval aig-eval-list
      aig-and aig-or aig-not aig-ite aig-xor aig-iff aig-nand aig-nor aig-andc1 aig-andc2 aig-orc1 aig-orc2

      defsvtv svtv-run svtv-debug svtv-easy-bindings svtv->ins svtv->vars svtv->outs svtv-p
      patbind-svtv


      ;; stuff for nicer documentation
      sv
      hardware-verification
      esim
      vl
      vl2014
      fty
      gl
      4v
      fast-alist
      fast-alists

      symlet)

    #!VL
    '(warnings
      warn
      fatal
      ok
      vl-warninglist-fix
      vl-warninglist-p
      make-vl-warning
      vl-printedlist-p
      vl-printedlist->string
      vl-printedlist-length
      vl-expr-p
      vl-expr-welltyped-p
      vl-atom-p
      xf-cwtime))

    ;; Things to remove:
    '(acl2::warn
      std::defalist
       std::deflist)))
