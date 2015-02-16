; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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

(in-package "VL2014")
(include-book "centaur/esim/vltoe/wirealist" :dir :system) ;; bozo
(include-book "../loader/parser/lvalues")
(include-book "../loader/lexer/lexer")
(include-book "../mlib/fmt")
(include-book "../lint/oddexpr") ;; bozo for *fake-modelement*
(include-book "../transforms/expr-size")
(local (include-book "../util/arithmetic"))


; BOZO this stuff should all be moved to proper files, e.g., commentmap,
; warnings, etc.

(define vl-uncomment-string
  :parents (use-set)
  :short "Eat the leading @('//') from a comment string, or eliminate the @('/*
... */') pair from a comment string."
  ((x stringp))
  :returns (new-x stringp :rule-classes :type-prescription)

  :long "<p>@('x') should be either a @('//')-style comment or a
@('/*...*/')-style comment; otherwise we just return it unchanged.  Typically
such strings are found in a @(see vl-commentmap-p).</p>

<p>If @('x') is a single-line comment (i.e., it literally starts with @('//'),
and note that we don't look past whitespace), then we strip the leading @('//')
but we don't strip any associated newline.</p>

<p>If @('x') is a multi-line comment (i.e., it literally starts with @('/*')
and ends with @('*/'), without looking at any whitespace), then we strip these
characters.</p>"

    (b* ((x  (string-fix x))
         (xl (length x))
         ((unless (and (>= xl 2)
                       (eql (char x 0) #\/)))
          x)
         ((when (eql (char x 1) #\/))
          (subseq x 2 nil))
         ((when (and (>= xl 4)
                     (eql (char x 1)        #\*)
                     (eql (char x (- xl 2)) #\*)
                     (eql (char x (- xl 1)) #\/)))
          (subseq x 2 (- xl 2))))
      x))

(define vl-comment-body-echars
  :parents (vl-commentmap-p)
  :short "Extract a comment's body as a @(see vl-echarlist-p)."
  ((x stringp "Should be either a @('//')-style comment or a @('/*...*/')-style
               comment.")
   (loc vl-location-p "Starting location to use for the comment's characters."))
  :returns (echars vl-echarlist-p)
  :long "<p>We strip these comment characters and turn the remaining characters
of @('x') into echars.  As a corner case, if @('x') isn't a Verilog comment, we
just turn the whole thing into echars.</p>

<p>Note from @(see vl-commentmap-p) that locations of comments are shifted over
and ordinarily aren't very reliable.  The locations in the resulting echars are
therefore also somewhat unreliable!</p>"

  (b* (((vl-location loc) loc)
       (x (vl-uncomment-string x))
       ;; This is kind of hideous but gives us an unconditional echarlist-p
       ;; result type theorem, which is nice.
       (filename (mbe :logic (string-fix loc.filename) :exec loc.filename))
       (line     (mbe :logic (if (posp loc.line) loc.line 1) :exec loc.line))
       (col      (lnfix loc.col)))
    (vl-echarlist-from-str x
                           :filename filename
                           :line line
                           ;; This is probably about the least-wrong thing we
                           ;; can do.
                           :col (+ 2 col))))

(define vl-prefix-warning
  :parents (warnings)
  :short "Add a prefix to a @(see vl-warning-p)'s message."
  ((prefix stringp)
   (x      vl-warning-p))
  :returns (new-warning vl-warning-p)
  (b* ((x (mbe :logic (if (vl-warning-p x)
                          x
                        (make-vl-warning :msg "Fake warning."))
               :exec x)))
    (change-vl-warning x :msg (cat prefix (vl-warning->msg x)))))

(defprojection vl-prefix-warnings (prefix x)
  (vl-prefix-warning prefix x)
  :guard (and (stringp prefix)
              (vl-warninglist-p x))
  :parents (warnings)
  ///
  (defthm vl-warninglist-p-of-vl-prefix-warnings
    (vl-warninglist-p (vl-prefix-warnings prefix x))))


(define vl-warninglist-change-types
  :parents (warnings)
  ((new-type symbolp          "New type for these warnings.")
   (x        vl-warninglist-p "Warnings to change."))
  :returns (new-x vl-warninglist-p :hyp :fguard)
  (if (atom x)
      nil
    (cons (change-vl-warning (car x) :type new-type)
          (vl-warninglist-change-types new-type (cdr x)))))


; Special comment syntax for use-set ignores.
;
; /* use_set_ignore ( foo, bar, baz[3:1] ); */
;
; We just piggy-back on our existing parsers.  I guess I'll parse these as
; lvalues.  I thought of parsing it as a concatenation but the lvalue parser is
; somewhat more restrictive and gives us an exprlist immediately, which is sort
; of nice.

(defparser us-parse-comment ()
  :result (vl-exprlist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (kwd := (vl-match-token :vl-idtoken))
       (unless (equal (vl-idtoken->name kwd) "use_set_ignore")
         (return-raw
          (vl-parse-error "Expected use_set_ignore keyword.")))
       (:= (vl-match-token :vl-lparen))
       (exprs := (vl-parse-1+-lvalues-separated-by-commas))
       (:= (vl-match-token :vl-rparen))
       (:= (vl-match-token :vl-semi))
       (return exprs)))

(define us-analyze-comment
; Ugh, this thing has just grown to require everything...
  ((x        stringp)
   (loc      vl-location-p)
   (ss       vl-scopestack-p)
   (walist   vl-wirealist-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings    vl-warninglist-p)
      (ignore-bits vl-emodwirelist-p :hyp (force (vl-wirealist-p walist))))

  (b* (((unless (str::substrp "use_set_ignore" x))
        ;; As a quick filter, don't bother analyzing the comment unless it actually
        ;; has a use_set_ignore in it somewhere.
        (mv (ok) nil))

       (locstr
        ;; Since the location's column probably isn't reliable (due to
        ;; comment shifting when we built the comment map; see
        ;; vl-commentmap-p), we don't want to print the actual LOC object for
        ;; any warnings.  Instead, LOCSTR just has the filename and line
        ;; number.
        (cat (vl-location->filename loc) ":" (natstr (vl-location->line loc))))

       ;; Now we try to parse the comment as a use_set_ignore(...);
       ;; directive.  I won't bother to do any preprocessing (what defines
       ;; would we even use?) but still have to lex, remove
       ;; comments/whitespace, and then finally try to parse the directive.
       ;; Ugh.  This is pretty hideous.
       (echars (vl-comment-body-echars x loc))

       ;; Lexing...
       ((mv okp tokens lwarnings) (vl-lex echars
                                          ;; bozo?
                                          :config *vl-default-loadconfig*
                                          :warnings nil))
       ((unless okp)
        (b* ((lwarnings (vl-warninglist-change-types :use-set-syntax-error lwarnings))
             (lwarnings (vl-prefix-warnings
                         (cat "Lexing error in comment at " locstr ", which mentions use_set_ignore, ")
                         lwarnings)))
          (mv (append lwarnings (vl-warninglist-fix warnings)) nil)))

       ;; Parsing...
       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
       ((local-stobjs tokstream) (mv warn res tokstream))
       (tokstream (vl-tokstream-update-tokens tokens))
       ((mv err exprs tokstream)
        (us-parse-comment :config *vl-default-loadconfig*))
       (tokens (vl-tokstream->tokens))
       ((when err)
        (b* ((details (with-local-ps (if (and (consp err)
                                              (stringp (car err)))
                                         (vl-cw-obj (car err) (cdr err))
                                       (vl-cw "Malformed error object: ~x0." err)))))
          (mv (warn :type :use-set-syntax-error
                    :msg (cat "Parsing error in comment at " locstr
                              ", which mentions use_set_ignore.  " details)
                    :args nil)
              nil tokstream)))
       (warnings
        (if (atom tokens)
            (ok)
          (warn :type :use-set-syntax-error
                :msg (cat "In comment at " locstr ", ignoring additional content after the "
                          "initial use_set_ignore(...); directive.")
                :args nil)))

       ;; If we get this far, we got the exprs parsed.  We need to look up their
       ;; sizes.  There's no context, and these should just be simple identifiers,
       ;; so just use exprlist-size.
       ((mv ?okp size-warnings exprs)
        (vl-exprlist-size exprs ss *fake-modelement* nil))
       (size-warnings (vl-warninglist-change-types :use-set-syntax-error size-warnings))
       (size-warnings (vl-prefix-warnings
                       (cat "Error sizing wires for use_set_ignore directive at " locstr ".  ")
                       size-warnings))
       (warnings (append size-warnings (vl-warninglist-fix warnings)))

       ;; Now try to turn the sized exprs into bits.  We try to return as
       ;; much as we can here, i.e., if the user writes use_set_ignore(foo,
       ;; bar, baz); and there's a problem with foo, we still want to ignore
       ;; bar/baz.
       ((mv ?okp bit-warnings bits) (vl-msb-exprlist-bitlist exprs walist nil))
       (bit-warnings (vl-warninglist-change-types :use-set-syntax-error bit-warnings))
       (bit-warnings (vl-prefix-warnings
                      (cat "Error looking up wires for use_set_ignore directive at " locstr ".  ")
                      bit-warnings))
       (warnings (append bit-warnings (vl-warninglist-fix warnings))))

    (mv warnings bits tokstream))
  ///
  (defmvtypes us-analyze-comment (nil true-listp))

  (local
   (defthm us-analyze-comment-grows-warnings
     ;; Since the warning handling above is subtle, I want to prove this
     ;; to make sure I didn't drop warnings.
     (let ((ret (us-analyze-comment x loc ss walist warnings)))
       (subsetp-equal (vl-warninglist-fix warnings)
                      (mv-nth 0 ret))))))

(define us-analyze-commentmap
  ((x        vl-commentmap-p)
   (ss       vl-scopestack-p)
   (walist   vl-wirealist-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (ignore-bits vl-emodwirelist-p :hyp (force (vl-wirealist-p walist))))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((cons loc str) (car x))
       ((mv warnings ignore-bits1)
        (us-analyze-comment str loc ss walist warnings))
       ((mv warnings ignore-bits2)
        (us-analyze-commentmap (cdr x) ss walist warnings)))
    (mv warnings (append ignore-bits1 ignore-bits2)))
  ///
  (defmvtypes us-analyze-commentmap (nil true-listp)))
