;; Readme.lsp file for the contribution books/concurrent-programs/german-protocol/

(
 (:files
 "
.:
  Makefile  
  Readme.lsp  
  ccp.m  
  german.lisp
"
 )
 (:TITLE "An ACL2 Proof of Coherence of the German Protocol")
 (:AUTHOR/S "Sandip Ray")
 (:Keywords "concurrent programs"
            "inductive invariant"
            "iterative strengthening"
            "directory-based cache system"
            )
 (:ABSTRACT

"This set of books definea an invariant that is strong enbough to verify the
coherence of the German Cache Protocol.  The proof shows how to come up with a
sufficient inductive invariant by iterative strengthening starting from the
desired base property.  The proof also demonstrates how to define invariant
predicates for multiprocess systems both using quantification over process
indices and recursive functions, thus providing a tutorial demonstration of how
to reason about concurrent protoicols."  
)
 (:PERMISSION

"An ACL2 Proof of Coherence of the German Protocol
Copyright (C) 2006 Sandip Ray

This program is free software; you can redistribute it and/ormodify it under
the terms of the GNU General Public Licenseas published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc., 51
Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA."
))

This set of books prvides an ACL2 proof of the German cache protocol.  The
protocol is translated directly into ACL2 from the murphy code provided in
ccp.m.  The proof involves formalizing coherence and strengthening the property
into an inductive invariant.

Background and Description
---------------------------

Anna Slobodova gave this problem to the author when she was looking for doing
cache protocol proofs with ACL2.  The key is that some predicates involved,
especially the key coherence property, could be naturally stated as quantified
formulas, and the question was how we could use the standard quantification
approaches together with (possibly) recursive functions to derive a proof in
the way the human would do.

I looked at the protocol and decided to do a proof on my own of the protocol in
ACL2.  Previously a similar proof ws done in ACL2 via predicate abstraction,
and this proof was primarily intended to show how predicate abstraction could
save labor over a standard ACL2 proof.  However, the ACL2 proof itself was not
devoid of interest, since it showed how one typically iterates over a partial
invariant to define a concrete inductive invariant for a protocol-level
system.  The proof did spring some surprises, for instance as documented in the
definition of some fragments of the invariant required in the proof.

However, the chief contribution of the proof is to provide a tutorial
introduction to coming up with an inductive invarriant for a complicated
multiprocess protocol.  Towards this end, substantial on-the-fly commentary of
the proof is provided in the form of comments, documenting the thought process
involved in the proof.  

For questions and concerns about these books, contact sandip@cs.utexas.edu.