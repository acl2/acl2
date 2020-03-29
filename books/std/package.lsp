; ACL2 Standard Library
; Copyright (c) 2008-2014 Centaur Technology
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

(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defconst *standard-acl2-imports*
  (set-difference-eq-exec
   (union-eq-exec (append
                   '(;; Some symbols ought to be included but aren't.
                     print-base-p
                     )
                   *acl2-exports*)
                  *common-lisp-symbols-from-main-lisp-package*)
   '(
     ;; Various string functions have nasty standard-char-p guards.  We remove
     ;; them from our packages because we don't want to accidentally try to use
     ;; them.  We especially want to keep these out of the STR package.
     upper-case-p
     lower-case-p
     char-upcase
     char-downcase
     string-upcase1
     string-downcase1
     string-upcase
     string-downcase

     ;; Various nice names have problematic definitions in Common Lisp and so
     ;; they are not ACL2 functions.  But that's no reason to import them into
     ;; our own packages.
     union
     delete
     find
     map
     set
     byte
     read
     write

     ;; Matt K. mod: rewrite-equiv was added 3/2020 to *acl2-exports but had
     ;; that addition caused the event (defprod rewrite ...) to fail in
     ;; centaur/meta/parse-rewrite.lisp; so we exclude that symbol here.
     rewrite-equiv
     )))

(defpkg "STR"
  (append '(simpler-take list-fix list-equiv rev
                         prefixp str b* assert! repeat replicate
                         listpos sublistp implode explode
                         a b c d e f g h i j k l m n o p q r s v x y z
                         top
                         defxdoc defsection lnfix definlined definline
                         define defines defaggregate
                         char-fix chareqv
                         str-fix streqv
                         raise
                         std
                         std/strings)
          *standard-acl2-imports*))

; Packages for the ordered sets library.  We should probably consolidate this
; stuff into the sets package, eventually.

(defpkg "INSTANCE" *standard-acl2-imports*)

(defpkg "COMPUTED-HINTS"
  (append '(mfc-ancestors
            mfc-clause
            INSTANCE::instance-rewrite)
          *standard-acl2-imports*))

(defpkg "SET"
  (append '(defsection
             defxdoc
             definline
             definlined
             lexorder
             lnfix
             <<
             <<-irreflexive
             <<-transitive
             <<-asymmetric
             <<-trichotomy
             <<-implies-lexorder
             fast-<<
             fast-lexorder
             COMPUTED-HINTS::rewriting-goal-lit
             COMPUTED-HINTS::rewriting-conc-lit
             def-ruleset
             def-ruleset!
             add-to-ruleset
             ;; makes :instance hints more convenient
             a b c d e f g h i j k l m n o p q r s t u v w x y z
             ;; for nicer (package-free) documentation links
             std/osets
             std)
          (set-difference-eq-exec
           *standard-acl2-imports*
           ;; [Changed by Matt K. to handle changes to member, assoc,
           ;;  etc. after ACL2 4.2 (intersectp was added to *acl2-exports*).]
           '(intersectp enable disable e/d))))

#!SET
(defconst *sets-exports*
  ;; This just contains the user-level set functions, and a couple of theroems
  ;; that frequently need to be enabled/disabled.
  '(<<
    setp
    empty
    sfix
    head
    tail
    insert
    in
    subset
    delete
    union
    intersect
    ;; intersectp -- we leave this out because of the existing ACL2 function
    ;; called intersectp.
    difference
    cardinality
    mergesort
    ;; A couple of theorems that frequently need to be enabled/disabled.
    double-containment
    pick-a-point-subset-strategy
    ))

(defpkg "XDOC"
  (append '(b* value defxdoc defxdoc-raw macro-args
               defpointer
               xdoc-extend defsection defsection-progn lnfix
               set-default-parents
               getprop formals justification def-bodies current-acl2-world def-body
               access theorem untranslated-theorem guard xdoc xdoc! unquote
               undocumented assert! top explode implode
               remove-equal-with-hint)
          set::*sets-exports*
          *standard-acl2-imports*))

(defconst *bitset-exports*
  '(bitsets
    bitset-singleton
    bitset-insert
    bitset-list
    bitset-list*
    bitset-delete
    bitset-union
    bitset-intersect
    bitset-difference
    bitset-memberp
    bitset-intersectp
    bitset-subsetp
    bitset-cardinality
    bitset-members

    equal-bitsets-by-membership
    bitset-witnessing
    bitset-equal-witnessing
    bitset-equal-instancing
    bitset-equal-example
    bitset-fns

    sbitsets
    sbitsetp
    sbitset-fix
    sbitset-members
    sbitset-singleton
    sbitset-union
    sbitset-intersect
    sbitset-difference
    ))

(defconst *bitsets-pkg-symbols*
  (append '(*bitset-exports*
            std
            std/util
            std/bitsets
            std/osets
            __function__
            raise
            define
            defines
            defrule
            rule
            defsection
            defxdoc
            defwitness
            definstantiate
            defexample
            include-raw
            witness
            xdoc
            assert!
            b*
            progn$

            enable*
            disable*
            e/d*
            set::enable
            set::disable
            set::e/d

            rev

            arith-equiv-forwarding
            lnfix
            lifix
            lbfix
            nat-equiv
            int-equiv

            logbitp-mismatch
            equal-by-logbitp
            logbitp-hyp
            logbitp-lhs
            logbitp-rhs

            a b c d e f g h i j k l m n o p q r s t u v w x y z
            )
          set::*sets-exports*
          *bitset-exports*
          (set-difference-eq-exec *standard-acl2-imports*
                                  '(intersectp enable disable e/d))))

(defpkg "BITSETS" *bitsets-pkg-symbols*)

(defconst *std-pkg-symbols*
  (append set::*sets-exports*

; Things I want to "export" to the ACL2 package.
;
; Should we export deflist, defalist, etc.?  On one hand, it would be nice NOT
; to export them since this makes these parts of the std library incompatible
; with books like data-structures/deflist.  On the other hand, it is ugly to
; type (std::deflist ...) instead of just deflist.
;
; I've gone back and forth on it.  I guess exporting them is bad.  I'll
; continue to export defsection and defmvtypes since they're unusually named
; and convenient, but for consistency all of the data-type introduction macros
; will be kept in the std package.

    '(std ; Makes ":xdoc std" do the right thing.
      std/util ;; likewise


      __function__
      raise
      tag
      tag-reasoning
      defsection
      defsection-progn
      defmvtypes
      rule
      defrule
      defruled
      defruledl
      defrulel
      define
      defines
      defconsts
      defval
      more-returns
      defret
      xdoc
;               defaggregate
;               defenum
;               defprojection
;               defmapappend
;               defalist
;               deflist

      ;; Things I want to "import" from ACL2 into the STD package.
      assert!
      must-fail
      b*
      ret
      def-b*-binder
      progn$
      simpler-take
      repeat
      replicate
      list-fix
      llist-fix
      rev
      rcons
      revappend-without-guard
      value
      two-nats-measure
      make-fal
      xdoc-extend
      legal-variablep
      set-equiv
      list-equiv
      never-memoize

      ;; BOZO consider moving these to std?
      defconsts
      definline
      definlined

      ;; BOZO why aren't these imported?
      strip-cadrs
      defxdoc

      uniquep
      duplicated-members

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

      ;; Stuff I moved into xdoc:
      xdoc::extract-keyword-from-args
      xdoc::throw-away-keyword-parts
      xdoc::mksym
      xdoc::mksym-package-symbol
      undocumented
      )
    *standard-acl2-imports*))

(defpkg "STD" *std-pkg-symbols*)

#!STD
(defconst *std-exports*
  '(std
    tag
    ret
    tag-reasoning
    defprojection
    deflist
    defalist
    defenum
    defaggregate
    defmapappend
    defmvtypes
    defsection
    defsection-progn
    defsum
    define
    defines
    rule
    defrule
    defruled
    defruledl
    defrulel
    defval
    defret
    defretd
    defconsts
    defxdoc
    raise
    __function__
    more-returns))

(assign acl2::verbose-theory-warning nil)

(defconst *stobjs-exports*
  ;; Things we want to "export" to the ACL2 package or other packages
  '(defabsstobj-events
    def-1d-arr
    def-2d-arr
    def-updater-independence-thm
    defstobj-clone
    new old))

(defpkg "STOBJS"
  (append '(
            ;; More things we want to import from the ACL2 package, because we're
            ;; going to use them internally
            *stobjs-exports*
            b* template-subst
            defmacfun deffunmac def-universal-equiv
            bit-equiv bfix bfix$inline
            enable* disable* e/d* e/d**
            def-ruleset def-ruleset! add-to-ruleset add-to-ruleset!
            arith-equiv-forwarding
            lnfix lifix lbfix nat-equiv int-equiv bit-equiv
            ;; for better documentation
            stobj stobjs abstract-stobj congruence equivalence bitarr
            std/stobjs
            )
          *stobjs-exports*
          std::*std-exports*
          *standard-acl2-imports*))

(defpkg "FLAG"
  (append '(getprop access def-body justification current-acl2-world
                    formals recursivep def-bodies
                    make-flag flag-present flag-fn-name flag-alist
                    flag-defthm-macro
                    flag-equivs-name
                    std::expand-calls-computed-hint
                    std::find-calls-of-fns-term
                    std::find-calls-of-fns-list
                    defxdoc defsection
                    b*
                    )
          (set-difference-eq acl2::*standard-acl2-imports*
                             '(id))))
