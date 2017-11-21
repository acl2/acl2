; APT Tail Recursion Transformation -- Design Notes
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/top" :dir :system)

; (depends-on "design-notes/tailrec.pdf")
; (depends-on "design-notes/notation.pdf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; documentation topic for the design notes,
; which are in design-notes/tailrec.pdf:

(defxdoc tailrec-design

  :parents (design-notes tailrec)

  :short "Design notes for the tail recursion transformation."

  :long

  "<p>
   The design of the transformation is described in
   <a href='res/apt/tailrec.pdf'>these notes</a>,
   which use <a href='res/apt/notation.pdf'>this notation</a>.
   </p>

   <p>
   The correspondence between the design notes and the reference documentation
   is the following:
   </p>

   <ul>

     <li>
     @($f$) corresponds to @('old').
     </li>

     <li>
     @($a(\\overline{x})$) corresponds to @('test<x1,...,xn>').
     </li>

     <li>
     @($b(\\overline{x})$) corresponds to @('base<x1,...,xn>').
     </li>

     <li>
     @($c(\\overline{x})$) corresponds to @('nonrec<x1,...,xn>').
     </li>

     <li>
     @($d_i(\\overline{x})$) corresponds to @('update-xi<x1,...,xn>').
     </li>

     <li>
     @($D$) corresponds to @('domain').
     </li>

     <li>
     @($*$) corresponds to @('combine').
     </li>

     <li>
     @($D{}b$) corresponds to @(':domain-of-base').
     </li>

     <li>
     @($D{}c$) corresponds to @(':domain-of-nonrec').
     </li>

     <li>
     @($D\\!*$) corresponds to @(':domain-of-combine').
     </li>

     <li>
     @($D\\!*'$) corresponds to @(':domain-of-combine-uncond').
     </li>

     <li>
     @($A{}S{}C$) corresponds to @(':combine-associativity').
     </li>

     <li>
     @($A{}S{}C'$) corresponds to @(':combine-associativity-uncond').
     </li>

     <li>
     @($L{}I$) corresponds to @(':combine-left-identity').
     </li>

     <li>
     @($R{}I$) corresponds to @(':combine-right-identity').
     </li>

     <li>
     @($G{}D$) corresponds to @(':domain-guard').
     </li>

     <li>
     @($G\\!*$) corresponds to @(':combine-guard').
     </li>

     <li>
     @($G{}D{}c$) corresponds to @(':domain-of-nonrec-when-guard').
     </li>

     <li>
     @($f'$) corresponds to @('new').
     </li>

     <li>
     @($\\tilde{f}$) corresponds to @('wrapper').
     </li>

     <li>
     @($f{}\\tilde{f}$) corresponds to @('old-to-wrapper').
     </li>

   </ul>

   <p>
   The decomposition of the recursive branch
   described in the reference documentation
   does not handle all the cases described in the design notes
   about the decomposition of the old function.
   </p>

   <p>
   The transformation requires the term @('base<x1,...,xn>')
   to be ground when the variant is @(':monoid') or @(':monoid-alt').
   The reason for this restriction is to avoid, for now,
   generating and using the function @($\\beta$) defined in the design notes.
   Thus, with the @(':monoid') or @(':monoid-alt') variants,
   the transformation is always in the special case of a ground base value
   described in the design notes.
   </p>

   <p>
   The transformation does not yet handle left and right identity independently,
   whose independent treatment is covered in the design notes.
   </p>")
