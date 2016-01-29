; VL Verilog Toolkit
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL")
(include-book "../util/warnings")
(include-book "../util/commentmap")

(defsection translate-off
  :parents (loader)
  :short "Warnings about comments like @('// synopsys translate_off')."

  :long "<p>Designs may occasionally contain special comments that certain
synthesis tools not to process a particular region.</p>

<p>These special comments are not part of the SystemVerilog standard and we
regard them as bad form.  VL does not give such comments any special treatment
and will act as though they are regular comments that have no effect on
semantics.</p>

<p>As a special measure, VL looks for suspicious comments to try to at least
warn you about them.  It should generally be straightforward to replace these
with appropriate @('`ifdef')s.</p>")

(local (xdoc::set-default-parents translate-off))

(define vl-scary-translate-comment-p ((x stringp))
  :short "Recognize special @('translate_off') or @('translate-on') comments."

  :long "<p>It seems as though different tools have different syntax for this.
From internet searches, it appears that at least the following may be used by
different tools:</p>

<ul>
<li>// synopsys translate_off</li>
<li>// synthesis translate_off</li>
<li>// pragma translate_off</li>
<li>// exemplar translate_off</li>
<li>// cadence translate_off</li>
</ul>

<p>As well as @('translate_on') versions of the above, as well as
@('/*...*/')-style instead of @('//')-style comments.  The above may well be
incomplete.</p>

<p>Well, it seems pretty reasonable to just flag any comment that mentions
@('translate_on') or @('translate_off').</p>"

  (or (str::substrp "translate_on" x)
      (str::substrp "translate_off" x)))

(define vl-commentmap-translate-off-warnings ((x vl-commentmap-p)
                                              (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  :measure (len (vl-commentmap-fix x))
  (b* ((x (vl-commentmap-fix x))
       ((when (atom x))
        (ok))
       ((cons loc comment) (car x))
       (warnings (if (vl-scary-translate-comment-p comment)
                     (warn :type :vl-warn-scary-translate-comment
                           :msg "~a0: ignoring a comment that may be a ~
                                  translate_on or translate_off directive.  ~
                                  Using a preprocessor directive like `ifdef ~
                                  ASSERT_ON is preferred.  Comment: ~s1"
                           :args (list loc comment))
                   (ok))))
    (vl-commentmap-translate-off-warnings (cdr x) warnings)))
