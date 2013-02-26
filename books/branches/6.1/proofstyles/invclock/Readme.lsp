;; Readme.lsp file for the contribution books/proofstyles

(
 (:files
 "
.:
  Makefile
  Readme.lsp
  c2i
  certify.lsp
  compose
  i2c

./c2i:
      Makefile
      c2i-partial.lisp
      c2i-total.lisp
      certify-c2i.lsp
      clock-to-inv.lisp

./compose:
          Makefile
          certify-compose.lsp
          compose-c-c-partial.lisp
          compose-c-c-total.lisp

./i2c:
      Makefile
      certify-i2c.lsp
      i2c-partial.lisp
      i2c-total.lisp
      inv-to-clock.lisp
"
 )
 (:TITLE "Books showing Equivalence of Proof Styles in Operational Semantics
         with ACL2")
 (:AUTHOR/S "Sandip Ray" "J Strother Moore")
 (:Keywords "total correctness"
            "partial correctness"
            "inductive invariants"
            "assertions"
            "clock functions")
 (:ABSTRACT

"The set of books here show that two proof styles used in theorem proving for
verifying programs using operational semantics. The two styles are the use of
inductive invariants and clock functions. We show that despite appearances the
two styles are logically equivalent in that given a proof in one style we can
mechanically generate a proof in the other. Both partial and total correctness
are considered." 
  )
 (:PERMISSION

"Proof Styles in Operational Semantics
Copyright (C) 2006 Sandip Ray and J Strother Moore

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

The  proofs developed in this set of books are described in the following
paper:

@Inproceedings{raymoore,
  author    = "S. Ray and J S. Moore",
  title     = "{Proof Styles in Operational Semantics}",
  editor    = "A. J. Hu and A. K. Martin",
  booktitle = "{Proceedings of the $5$th International Conference on
                Formal Methods in Computer-Aided Design (FMCAD 2004)}",
  series    = "{LNCS}",
  volume    = "3312",
  address   = "{Austin, TX}",
  publisher = "{Springer-Verlag}",
  month     = nov,
  pages     = "67-81",
  year      = 2004
}

The books were developed in 2003, influenced by the then recent paper by Moore
(bibtex entry below) showing how inductive assertion style reasoning could be
performed on operational semantics.

@Inproceedings{jm:indop,
  author    = "J S. Moore",
  title     = "{Inductive Assertions and Operational Semantics}",
  booktitle = "{Proceedings of the $12$th International Conference
                on Correct Hardware Design and Verification Methods}",
  editor    = "D. Geist",
  series    = "{LNCS}",
  publisher = "{Springer-Verlag}",
  month     = oct,
  volume    = "2860",
  pages     = "289-303",
  year      = 2003
}

In February 2003, Moore presented his inductive assertions work at the ACL2
seminar, and (informally) challeged the attendees to come up with a way of
using clock functions for doing inductive assertions proofs. Ray answered the
challenge in around March 2003, by defining primitive versions of the books
here, that showed that one can mechanically translate one proof style to the
other. Subsequently Ray and Moore improved these to general-purpose books that
could be used to reason about exits from program components as well. This all
was then written up and published as a paper in the proceedings of FMCAD 2004.


Background and Contributions:

Clock functions have been used for long in the Boyer-Moore community for doing
code proofs. However, they have been rarely used anywhere else. There have been
lots of criticisms for clocks. It was believed that clocks prove something more
than "just" correctness, and that clocks make the user do extra work.

This set of books shows that neither belief is correct. Given a more
traditional proof we can translate it mechanically to a clock version and vice
versa. The set of books includes macros that mechanically generate such
transformations.

Miscellaneous comments:

To certify everything, either
(i) run make, or
(ii) start up acl2 from this directory and do (ld "certify.lsp")

The books are documented. A good place to start reading the proofs is the
directory i2c/, where the book i2c-total.lisp contains extensive comments
(being the start of the endeavor). The documentation in the rest of the books
assumes that you have read and understood these inital comments.

For questions and concerns about these books, contact sandip@cs.utexas.edu.