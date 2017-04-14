; ABNF Library
;
; Copyright (C) 2016-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides a library for ABNF (Augmented Backus-Naur Form).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "abstract-syntax")
(include-book "semantics")
(include-book "operations")
(include-book "core-rules")
(include-book "concrete-syntax")
(include-book "parser")
(include-book "abstractor")
(include-book "parser-and-abstractor-validation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc abnf

  :parents (acl2::kestrel-books)

  :short "A library for ABNF (Augmented Backus-Naur Form)."

  :long

  "<p>
   ABNF is a standardized formal grammar notation
   used in several Internet syntax specifications,
   e.g.
   <a href=\"https://www.rfc-editor.org/info/rfc3986\">URI</a>,
   <a href=\"https://www.rfc-editor.org/info/rfc7230\">HTTP</a>,
   <a href=\"https://www.rfc-editor.org/info/rfc5322\">IMF</a>,
   <a href=\"https://www.rfc-editor.org/info/rfc5321\">SMTP</a>,
   <a href=\"https://www.rfc-editor.org/info/rfc3501\">IMAP</a>, and
   <a href=\"https://www.rfc-editor.org/info/rfc7159\">JSON</a>.
   ABNF is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc5234\">RFC 5234</a> and
   <a href=\"https://www.rfc-editor.org/info/rfc7405\">RFC 7405</a>;
   the latter updates two portions of the former.
   The syntax of ABNF is specified in ABNF itself.
   </p>

   <p>
   This ACL2 library provides:
   </p>
   <ul>
     <li>
     A formalization of the syntax and semantics of the ABNF notation.
     </li>
     <li>
     A verified parser that turns ABNF grammar text
     (e.g. from the HTTP RFC)
     into a formal representation suitable for formal specification
     (e.g. for HTTP parsing).
     </li>
     <li>
     Executable operations on ABNF grammars,
     e.g.\ to check their well-formedness and to compose them.
     </li>
   </ul>

   <p>
   In the documentation of this library,
   we append dotted section and subsection numbers to &lsquo;RFC&rsquo;
   to refer to the corresponding sections and subsections
   of the result of updating RFC 5234 as specified by RFC 7405.
   For example, &lsquo;RFC.3&rsquo; refers to Section 3 of RFC 5234.
   As another example, &lsquo;RFC.2.3&rsquo; refers to
   the result of updating Section 2.3 of RFC 5234
   as specified in Section 2.1 of RFC 7405.
   </p>")

(xdoc::order-subtopics abnf nil t)
