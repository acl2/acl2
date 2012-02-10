((:files
"
.:
Makefile
Readme.lsp
bstar.lisp
cws.lisp
def-functional-instance.lisp
defconsts.lisp
defevaluator-fast.lisp
define-keyed-function.lisp
defined-const.lisp
defsum.lisp
deftuple.lisp
do-not.lisp
fake-event.lisp
flag.acl2
flag.lisp
flag-package.lsp
index.html
include-raw.lisp
mv-nth.lisp
oracle-eval.acl2
oracle-eval.lisp
oracle-eval-real.acl2
oracle-eval-real.lisp
pack.lisp
plev.lisp
plev-ccl.lisp
plev-ccl-raw.lsp
progndollar.lisp
rulesets.lisp
safe-case.lisp
saved-errors.lisp
stobj-help.lisp
theory-tools.lisp
time-dollar-with-gc-raw.lsp
time-dollar-with-gc.lisp
types-misc.lisp
with-arith5-help.lisp
with-quoted-forms.lisp
")
 (:TITLE "Tools")
 (:AUTHOR/S
  "Sol Swords"
  "Jared Davis"
  "David L. Rager"
  )
 (:KEYWORDS
  "macro"
  )
 (:ABSTRACT "The books in this directory contain miscellaneous macros
and tools designed to make common constructs easier and less verbose
to write.  See index.html for more detailed documentation than this
abstract, and comments in the source files for more yet.

bstar.lisp defines the macro B* which is a drop-in replacement for
LET* with support for binding MVs and recognizing user-defined binder
forms.

cws.lisp defines CWS, which is a shortcut for printing expressions and
their values without typing formatting strings.

def-functional-instance.lisp provides a simple utility for proving
functional instantiations of existing theorems.

defconsts.lisp defines DEFCONSTS, which is like defconst but can cope
with functions that return multiple values.

defined-const.lisp defines DEFINED-CONST, which produces a defconst
and a theorem saying what term it represents while only evaluating
that term once (if the HONS system is present) or twice (if not.)

define-keyed-function.lisp defines macro DEFKUN, which defines a
macro and function pair that allow a programming style of passing
keyword arguments to function calls.

defevaluator-fast.lisp provides a macro much like defevaluator, but
much faster when the number of functions to be recognized is large.

do-not.lisp provides DO-NOT-HINT, a computed hint that can give
:do-not and :do-not-induct hints throughout several proofs to reduce your
typing burden.

fake-event.lisp provides a function that runs an event but does not store
it in the world.

include-raw.lisp provides a tool to load raw Lisp files inside books,
compiling them on book certification, handling errors, etc.  A TTAG is
required.

in-raw-mode.lisp provides a wrapper for running raw Lisp events. A TTAG is
required.

progndollar.lisp defines PROGN$, which evaluates several forms in
sequence for side effects.

plev.lisp (and plev-ccl.lisp/plev-ccl-raw.lsp) provide PLEV, PLEV-MIN,
and PLEV-MAX for controlling printing.

safe-case.lisp is a drop-in replacement for case, but causes an error
if none of the cases are matched.

saved-errors.lisp provides a way of customizing error messages for
complex generated events.

defsum and deftuple.lisp provide macros for defining product types
with constructors, accessors, recognizers, and appropriate theorems
for reasoning about them without reference to the underlying cons
representation.  DEFSUM defines a recursive sum-of-products type,
whereas DEFTUPLE defines a simple product type (tuple.)
Types-misc.lisp and theory-tools.lisp both exist primarily as support
for defsum and deftuple.

oracle-eval.lisp provides a logic-mode function that can evaluate
ACL2 terms that return a single non-stobj value.  The logic definition
of this function just reads the oracle, and so nothing is known about
its result.

pattern-match.lisp provides user-extensible pattern-matching
functionality, especially useful for writing functions that deal with
sum-of-products data structures as defined by defsum.

stobj-help.lisp provides a make-event which proves some useful rules
about a stobj, such as type theorems, access/update rewrite rules,
etc.

time-dollar-with-gc.lisp provides a time$-with-gc macro that reports both
timing and garbage collection information.

with-quoted-forms.lisp provides a macro that may be useful for
computing complicated :USE hints where the terms used in the
substitutions result from deeply nested variable bindings.
")
 (:PERMISSION
  "{bstar,cws,defined-const,defsum,deftuple,pack,progndollar,theory-tools,types-misc}.lisp
 copyright (C) 2009 by Sol Swords <sswords@cs.utexas.edu>.

{define-keyed-function,time-dollar-with-gc}.lisp copyright (C) 2010, 2011 by
David L. Rager <ragerdl@cs.utexas.edu>.

{plev,plev-ccl}.* were originally in misc/hons-help and are presumably
copyright (C) Bob Boyer and Warren Hunt.

{def-functional-instance,defconsts,flag,oracle-eval,safe-case,include-raw,
 fake-event}.lisp
copyright
2008-2011 by Centaur Technology

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 2 of
the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public
License along with this program; if not, write to the Free
Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
Boston, MA 02110-1301, USA."))
