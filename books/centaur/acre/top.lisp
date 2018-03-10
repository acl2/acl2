; Centaur regular expression library
; Copyright (C) 2014 Centaur Technology
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

(in-package "ACRE")

(include-book "parse")
(include-book "match")
(local (xdoc::set-default-parents acre-internals))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable take (tau-system))))



(define parse-and-match-regex ((pat stringp "String to parse as a regular expression")
                               (x stringp "String to match against")
                               &key
                               ((case-insens booleanp "Match case-insensitively") 'nil)
                               ((legible booleanp "Option to preprocess
                                                   away non-escaped whitespace
                                                   and Perl-style @('#')
                                                   comments") 't))
  :parents (acre)
  :short "Parse a regular expression from a pattern string and match it against a string @('x')."
  :long "<p>Same as @(see parse) followed by @(see match-regex).</p>"
  :returns (mv (parse-err acl2::maybe-stringp :rule-classes :type-prescription
                          "Parse error message")
               (match matchresult-p
                      "Result of matching, including whether it matched,
                                 which part matched, and capture group matches")) 
  (b* (((mv err regex) (parse pat :legible legible))
       ((when err) (mv err (make-matchresult :loc nil :len 0 :str x :backrefs nil))))
    (mv nil (match-regex regex x :case-insens case-insens)))
  ///
  (defret matchresult-in-bounds-of-<fn>
    (matchresult-in-bounds match)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable matchresult-in-bounds)))))

  (defret matchresult->str-of-<fn>
    (equal (matchresult->str match) (lstrfix x))))


(defmacro match (pat x &key (case-insens 'nil) (legible 't))
  (b* (((unless (stringp pat))
        (er hard? 'match "Expected pattern to be a string"))
       ((unless (booleanp legible))
        (er hard? 'match "Expected legible to be a Boolean"))
       ((mv err regex) (parse pat :legible legible))
       ((when err) (er hard? 'match "Parse error: ~s0" err)))
    `(match-regex ',regex ,x :case-insens ,case-insens)))

(defxdoc match
  :parents (acre)
  :short "Match a string against a regular expression, which is parsed at macroexpansion time."
  :long "<p>Signature:</p>
@({
 (match pattern str :case-insens nil :legible t)
 --> match-result
 })

<p>This macro runs @(see parse) at macroexpansion time to create a regular
expression object that is \"compiled in\" to the function, so that parsing
doesn't need to be done every time.  This means that the input pattern must be
a string literal and legible must be a Boolean literal.  If the regular
expression is malformed, it will result in an error at macroexpansion
time.</p>")



