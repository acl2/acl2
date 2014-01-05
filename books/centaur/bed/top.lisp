; Centaur BED Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "BED")
(include-book "ops")
(include-book "eval")
(include-book "mk1")
(include-book "aig")
(include-book "print")
(include-book "up")

(defsection bed
  :parents (acl2::boolean-reasoning)
  :short "A Hons-based implementation of Boolean Expression Diagrams, described
by Anderson and Hulgaard."

  :long "<p>NOTE: this is a preliminary, work in progress.  We do not recommend
using this library for anything, yet.</p>

<p>In this library we represent BEDs using a Hons-based approach similar to
@(see acl2::ubdds) or @(see acl2::aig)s.  You would ordinarily expect a BED to
be represented as a DAG.  We instead use HONS to make the DAG explicit.  This
allows us to refer to particular nodes in the graph as if they were individual
expressions, and makes it much easier to reason about BEDs.  It is likely that
an approach like @(see aignet::aignet) could be used to develop a faster BED
implementation, but we think this would be a lot more work.</p>

<p>BEDs are a non-canonical representation.  The basic idea of our
representation is:</p>

@({
     Bed ::= Atom                     ; Terminal node
           | (VAR . (LEFT . RIGHT))   ; Variable ITE node
           | ((LEFT . RIGHT) . OP)    ; Binary operator node
})

<p>In the \"well-formed\" case:</p>

<ul>
<li>All terminals are Booleans, i.e., @('t') or @('nil')</li>
<li>The variable names are any ACL2 atoms</li>
<li>The operators are valid @(see bed-op-p)s.</li>
</ul>

<p>But we don't have an explicit @('bed-p') recognizer and we can interpret any
ACL2 object as a BED:</p>

<ul>

<li>Any atom is coerced into a well-formed terminal using, e.g., @('(if x t
nil)').</li>

<li>Any improper operator is coerced into a @(see bed-op-p) using @(see
bed-op-fix).</li>

<li>In any (var . atom) pair, the atom is interpreted as (nil . nil).</li>

</ul>

<p>This representation is a little goofy, but it has been carefully designed.
Allowing any ACL2 object as a BED means that we don't need a @('bed-p')
recognizer and can avoid memoized checks of beds for well-formedness.  Our
goofy interpretation of the cons cases keeps each node to only two conses,
without any ambiguity between variables and operators.  Finally, checking
@('atom') is fast, so we can quickly distinguish variable from operator
nodes.</p>")

