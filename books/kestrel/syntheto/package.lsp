; Syntheto Library
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; if we want to use *std-pkg-symbols*
(include-book "std/portcullis" :dir :system)
;; if we want to add fty symbols
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/apt/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Syntheto, the language, does not yet have a source level package concept.

;; Syntheto, the language, is translated into ACL2 definitions.
;; The names of those definitions (and only the names of those definitions)
;; are in the special package SYNDEF so that
;; (1) we do not worry about name conflicts between Syntheto and ACL2 system
;;     definitions; and
;; (2) name conflicts on Syntheto definitions can be correctly reported.

(defpkg "SYNDEF" '(
            ;; Potentially, predefined system functions that are treated like user-defined
            ;; functions could go here.
            ;; (There aren't any yet.)
            )
  "Package for names of Syntheto definitions.")

#||
NOTES ON THE SYNDEF PACKAGE
Please add any ideas here.

If the name of a type is in SYNDEF, the recognizer, fixing function, and equiv
function will also all be (exclusively) in the SYNDEF package.
Field names are required to be in the SYNDEF package.
Additionally, the constructor and field selectors will be there.
This all may change, however...

If a defprod name is in SYNDEF, e.g.,
  (make-record-type syndef::rec (syndef::fieldname pos) ..)
which expands into
  (fty::defprod syndef::rec ((syndef::fieldname fieldtype) ..))
the obvious expected symbols in SYNDEF are:
  REC REC-P REC-FIX REC-EQUIV FIELDNAME
and then the other symbols mentioned in the documentation:
  MAKE-REC CHANGE-REC REC->FIELDNAME
but then there are around 40 more symbols, some of which make sense,
like
  REC-COUNT REC-P-OF-REC-FIX
but others look to be accidental, like
  X Y Z NEW-X X-EQUIV

At some point in the future, the rules for names in Syntheto
will need to be made precise.  There are a lot of symbols created
by fty::defprod, fty::deftagsum, etc.  Probably at some point
those will need to be put in a different package from the definition symbol
so that the semantics of Syntheto can be precise.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

More thoughts on the packages,
in relation to the shallow embedding macros
submitted to ACL2,
by Eric M 2020-09-30.

We want the syntheto code to be non-package-sensitive.
So something like
def myfn (x: int, y: myprod): r: string =
  if x == y.myfield then "YES" else "NO"

This will turn into an s-expression that is parsed by the ACL2 reader.
By default the bridge listener will parse it in the ACL2 package,
and we don't plan to change that anytime soon.

Since we want the definition names to avoid collisions with ACL2 names
we would like names like MYFN to either be parsed in the SYNDEF package or to
be converted to the SYNDEF package.  To convert them, we can either
make them strings (with the potential cumbersome aspect of having
lots of escaped string quotes) or put them in the keyword package.

We also have to think about the let-binding names, which package should
they go in?  Since ACL2 is a lisp-2 we don't have to worry about collisions
between var names and function names, so we could put those in SYNDEF as well.
But if we have to say SYNDEF::X in a lot of places, that is inconvenient for
the front end developer.  I would prefer that even the shallow macros
not have package prefixes.

There are also different contexts that could specify symbols differently.
* For example, in expressions (in the shallow macro language),
  "X" is the literal string, but (s-varref "X") expands to the variable SYNDEF::X.
  That is fine.
* But in function definitions, we have param lists like
  ((X INT) (Y MYPROD)) with many possible representations.
  First of all, we don't want to parse this in the ACL2 package
  because we don't want to intern X, Y, and MYPROD in the ACL2 package.
  But we are not changing the package.
  So the alternatives are strings or keyword symbols.
  Which is better?
  (("X" "INT") ("Y" "MYPROD"))
  or
  ((:X :INT) (:Y :MYPROD))
  I'm tending towards strings, because the colon is more distracting
  to most front-end developers (it usually is a separator, and the
  whitespace following it is not significant, whereas here,
  whitespace will change the meaning).

If we want to support case-sensitive names, the choice would be between
"HTYGjEAz" vs :|HTYGjEAz|

Here are some possible defining macros:

1. use strings for
(s-fun "MYFN" :inputs (("X" "INT") ("Y" "MYPROD"))
              :outputs (("R" "STRING"))
              :body (s-if (s-equal (s-varref "X") ..)
                          "YES" "NO") ; these strings are literal strings
    )

We are sticking with the "ACL2" package for reading these.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Yet more thoughts on the packages,
in relation to the shallow embedding macros
and bridge listener thread parsing
submitted to ACL2,
by Eric M 2020-10-02.

* parsing package remains ACL2

* symbols with no explicit package prefix are just the defining macros, and they
  should be imported into SYNTHETO at package definition time

* predefined base type names, recognizer predicates, fixing functions,
  and equiv functions should be imported into SYNTHETO at package definition
  time

* predefined base type names should also be imported into SYNDEF at
  package definition time, to maintain consistency with new type names
  In the text sent to the bridge, these type names should have their package
  prefix "SYNDEF::".

* names of user-defined things: named composite types, function names,
  parameter names, and local variable names, should all have SYNDEF:: preceding
  them.

* names of things that don't show up in user code will generally be in
  SYNTHETO; however, derived symbols like the recognizer predicate for a
  defprod will automatically be in the same package as the type name,
  so they will be in SYNDEF.  This could cause a problem, for example
  if someone wanted to define defprod FOO and then later FOO-P.
  We can revisit this issue later.

* auto-generated type names for unnamed types go into the SYNTHETO package.
  These would not be seen by the bridge parser.
  We could forbid user-defined types named SET, SEQ, MAP, and OPT, so
  that the auto-generated type names can be easily parsed.  Is that OK?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2020-10-02 part 2
;; Oops!  Supersedes all of the above.
;; We want the Syntheto language to be case-sensitive.
;; The shallow embedding macro language will then need to refer to user-defined
;; names using either strings or vertical bars around the symbols.
;; If it is strings, then we need to disambiguate user-defined name strings
;; from literal strings, but wrapping either or both with something.
;; In the case of literal names, in most cases they already have wrappers around
;; a string.  E.g. s-let and s-call.  So, let's do that explicitly throughout.
;; Even type names should have this.
;; So, generally, there should not be any symbols in the serialized
;; S-expression sent to the bridge except those naming the shallow macros.

;; What do we do about the base types?
;; Front end turns them in to 0-ary macros:
;;   (s-type-int), (s-type-bool), (s-type-char), (s-type-string)
;; which expand into the appropriate type symbols, none of which should be in the
;; SYNDEF package.
;; Named type references, on the other hand, are specified as (s-type-ref "myprod")
;; which means that they go into the SYNDEF package.

;; The Syntheto grammar should make sure that nobody can define a named type
;; with the same concrete syntax name as a predefined base type.  By this,
;; I mean before lisp sees it at all.  If the syntax for a string type is
;; "string", then the grammar should disallow "structure string ..", for
;; example, but "structure String .." could be OK (although discouraged).
;; Then when the front end sees a type ref such as in "foo: string"
;; it turns that into (s-type-string), and when it sees a type ref such as in
;; "foo: String", it turns that into (s-type-ref "String").

||#



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The SYNTHETO package is for code that processes Syntheto definitions.
;;
;; Therefore this package is now for the code that processes Syntheto.

(defpkg "SYNTHETO"
  (append (set-difference-eq
           *std-pkg-symbols* ;; *standard-acl2-imports*
           '( ;; removed symbols
             check-type
             function
             functionp
             program
             subtypep
             type
             typep
             ))

          '(
            ;; other commonly used symbols from the "ACL2" package:
            defxdoc+
            defmacro+
            pseudo-event-formp
            er-soft+

            ;; for guard obligations for unreachable code:
            impossible

            ;; Base type symbols, from xdoc basetypes.
            ;; Some already in *std-pkg-symbols*, but it is OK to duplicate.

            bit bitp bfix bit-equiv
            nat natp nfix nat-equiv
            int integerp ifix int-equiv
            rational rationalp rfix rational-equiv
            acl2-number ACL2-numberp fix number-equiv
            true-list true-listp list-fix list-equiv
            string stringp str-fix streqv
            true true-p true-fix true-equiv
            symbol symbolp symbol-fix symbol-equiv
            pos posp pos-fix pos-equiv
            character characterp char-fix chareqv
            any any-p identity equal
            bool booleanp bool-fix iff
            maybe-nat maybe-natp maybe-natp-fix maybe-nat-equiv
            maybe-pos maybe-posp maybe-posp-fix maybe-pos-equiv
            maybe-bit maybe-bitp maybe-bit-fix maybe-bit-equiv
            maybe-integer maybe-integerp maybe-integerp-fix maybe-integer-equiv

            ;; EM 2020-09-23:
            ;; Since at first we will assume (current-package state) is "ACL2",
            ;; let's intern the simple macro names to ACL2 and then
            ;; share them with syntheto.  It will be easier for the IDE
            ;; developers not to have to put "SYNTHETO::" on everything.
            s-type-boolean
            s-type-integer
            s-type-character
            s-type-string
            s-type-ref

            make-product-type
            make-sum-type
            make-option-type
            make-set-type
            make-sequence-type
            make-map-type

            make-subtype

            ;; expression macros.  Same note as above (09-23) on packages.
            s-literal-true s-literal-false
            s-literal-char
            s-varref
            s-not s-negate
            s-equal s-notequal
            s-gt s-gte s-lt s-lte
            s-and s-or
            s-plus s-minus
            s-times s-div s-rem
            s-conditional
            s-call

            #|| for now, let's refer to these with their package prefixes
                to make it clear
            fty::defprod
            fty::deftypes
            fty::deftagsum
            fty::defflexsum
            fty::deffixtype
            fty::deffixequiv
            fty::deffixequiv-mutual
            fty::defoption
            fty::deftranssum
            ||#

            )))
