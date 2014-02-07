; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../loader/parser/lvalues")
(include-book "../loader/lexer/lexer")
(include-book "../mlib/fmt")
(include-book "../checkers/oddexpr") ;; bozo for *fake-modelement*
(include-book "../toe/toe-wirealist")
(include-book "../transforms/xf-sizing")
(local (include-book "../util/arithmetic"))


; BOZO this stuff should all be moved to proper files, e.g., commentmap,
; warnings, etc.

(defsection vl-uncomment-string
  :parents (vl-commentmap-p)
  :short "Eat the leading @('//') from a comment string, or eliminate the @('/*
... */') pair from a comment string."

  :long "<p><b>Signature:</b> @(call vl-uncomment-string) returns a string.</p>

<p>@('x') must be a string.  It should be either a @('//')-style comment or a
@('/*...*/')-style comment; otherwise we just return it unchanged.  Typically
such strings are found in a @(see vl-commentmap-p).</p>

<p>If @('x') is a single-line comment (i.e., it literally starts with @('//'),
and note that we don't look past whitespace), then we strip the leading @('//')
but we don't strip any associated newline.</p>

<p>If @('x') is a multi-line comment (i.e., it literally starts with @('/*')
and ends with @('*/'), without looking at any whitespace), then we strip these
characters.</p>"

  (defund vl-uncomment-string (x)
    (declare (type string x))
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

  (defthm stringp-of-vl-uncomment-string
    (stringp (vl-uncomment-string x))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-uncomment-string)))))



(defsection vl-comment-body-echars
  :parents (vl-commentmap-p)
  :short "Get the body of a comment as a @(see vl-echarlist-p)."
  :long "<p><b>Signature:</b> @(call vl-comment-body-echars) returns an @(see
vl-echarlist-p).</p>

<p>@('x') must be a string.  It should be either a @('//')-style comment or a
@('/*...*/')-style comment.  We strip these comment characters and turn the
remaining characters into echars.  If @('x') isn't a Verilog comment, we just
turn the whole thing into echars.</p>

<p>The @('loc') is a location to use as the starting location for these
comment's characters.  However, note from @(see vl-commentmap-p) that locations
of comments are shifted over and ordinarily aren't very reliable.  The
locations in the resulting echars are therefore also somewhat unreliable!</p>"

  (local (defthm l0 ;; always more stupid crap
           (implies (and (<= 0 a)
                         (<= 0 b))
                    (<= 0 (+ a b)))))

  (defund vl-comment-body-echars (x loc)
    (declare (type string x)
             (xargs :guard (vl-location-p loc)))
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

  (defthm vl-echarlist-p-of-vl-comment-body-echars
    (vl-echarlist-p (vl-comment-body-echars x loc))
    :hints(("Goal" :in-theory (e/d (vl-comment-body-echars)
                                   ((force)))))))



(defsection vl-prefix-warning
  :parents (warnings)
  :short "@(call vl-prefix-warning) adds the given @('prefix') to the message
for warning @('x'), creating a new, extended warning."

  (defund vl-prefix-warning (prefix x)
    (declare (type string prefix)
             (xargs :guard (vl-warning-p x)))
    (change-vl-warning x :msg (cat prefix (vl-warning->msg x))))

  (defthm vl-warning-p-of-vl-prefix-warning
    (implies (force (vl-warning-p x))
             (vl-warning-p (vl-prefix-warning prefix x)))
    :hints(("Goal" :in-theory (enable vl-prefix-warning)))))


(defprojection vl-prefix-warnings (prefix x)
  (vl-prefix-warning prefix x)
  :guard (and (stringp prefix)
              (vl-warninglist-p x))
  :result-type vl-warninglist-p
  :parents (warnings))




(defsection vl-warninglist-change-types
  :parents (warnings)
  :short "@(call vl-warninglist-change-types) changes the @('type') of every
warning in the list @('x') to @('new-type')."

  (defund vl-warninglist-change-types (new-type x)
    (declare (xargs :guard (and (symbolp new-type)
                                (vl-warninglist-p x))))
    (if (atom x)
        nil
      (cons (change-vl-warning (car x) :type new-type)
            (vl-warninglist-change-types new-type (cdr x)))))

  (defthm vl-warninglist-p-of-vl-warninglist-change-types
    (implies (and (symbolp new-type)
                  (vl-warninglist-p x))
             (vl-warninglist-p (vl-warninglist-change-types new-type x)))
    :hints(("Goal" :in-theory (enable vl-warninglist-change-types)))))



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
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-idtoken))
        (unless (equal (vl-idtoken->name kwd) "use_set_ignore")
          (return-raw
           (vl-parse-error "Expected use_set_ignore keyword.")))
        (:= (vl-match-token :vl-lparen))
        (exprs := (vl-parse-1+-lvalues-separated-by-commas))
        (:= (vl-match-token :vl-rparen))
        (:= (vl-match-token :vl-semi))
        (return exprs)))

(defsection us-analyze-comment

; Ugh, this thing has just grown to require everything...

  (defund us-analyze-comment (x loc mod ialist walist warnings)
    "Returns (MV WARNINGS' IGNORE-BITS)"
    (declare (type string x)
             (xargs :guard (and (vl-location-p loc)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings))))
    (b* (((unless (str::substrp "use_set_ignore" x))
          ;; As a quick filter, don't bother analyzing the comment unless it actually
          ;; has a use_set_ignore in it somewhere.
          (mv warnings nil))

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
            (mv (append lwarnings warnings) nil)))

         ;; Parsing...
         ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
         ((mv err exprs tokens ?pwarnings)
          (us-parse-comment :tokens tokens
                            :warnings nil
                            :config *vl-default-loadconfig*))
         ((when err)
          (b* ((details (with-local-ps (if (and (consp err)
                                                (stringp (car err)))
                                           (vl-cw-obj (car err) (cdr err))
                                         (vl-cw "Malformed error object: ~x0." err))))
               (w (make-vl-warning
                   :type :use-set-syntax-error
                   :msg (cat "Parsing error in comment at " locstr
                             ", which mentions use_set_ignore.  " details)
                   :args nil
                   :fatalp nil
                   :fn 'us-analyze-comment)))
            (mv (cons w warnings) nil)))
         (warnings
          (b* (((when (atom tokens))
                warnings)
               (w (make-vl-warning
                   :type :use-set-syntax-error
                   :msg (cat "In comment at " locstr ", ignoring additional content after the "
                             "initial use_set_ignore(...); directive.")
                   :args nil
                   :fn 'us-analyze-comment
                   :fatalp nil)))
            (cons w warnings)))

         ;; If we get this far, we got the exprs parsed.  We need to look up their
         ;; sizes.  There's no context, and these should just be simple identifiers,
         ;; so just use exprlist-size.
         ((mv ?okp size-warnings exprs)
          (vl-exprlist-size exprs mod ialist *fake-modelement* nil))
         (size-warnings (vl-warninglist-change-types :use-set-syntax-error size-warnings))
         (size-warnings (vl-prefix-warnings
                         (cat "Error sizing wires for use_set_ignore directive at " locstr ".  ")
                         size-warnings))
         (warnings (append size-warnings warnings))

         ;; Now try to turn the sized exprs into bits.  We try to return as
         ;; much as we can here, i.e., if the user writes use_set_ignore(foo,
         ;; bar, baz); and there's a problem with foo, we still want to ignore
         ;; bar/baz.
         ((mv ?okp bit-warnings bits) (vl-msb-exprlist-bitlist exprs walist nil))
         (bit-warnings (vl-warninglist-change-types :use-set-syntax-error bit-warnings))
         (bit-warnings (vl-prefix-warnings
                        (cat "Error looking up wires for use_set_ignore directive at " locstr ".  ")
                        bit-warnings))
         (warnings (append bit-warnings warnings)))

      (mv warnings bits)))

  (local (in-theory (enable us-analyze-comment)))

  (defmvtypes us-analyze-comment (nil true-listp))

  (defthm vl-warninglist-p-of-us-analyze-comment
    (let ((ret (us-analyze-comment x loc mod ialist walist warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 ret)))))

  (local
   (defthm us-analyze-comment-grows-warnings
     ;; Since the warning handling above is subtle, I want to prove this
     ;; to make sure I didn't drop warnings.
     (let ((ret (us-analyze-comment x loc mod ialist walist warnings)))
       (subsetp-equal warnings (mv-nth 0 ret)))))

  (defthm vl-emodwirelist-p-of-us-analyze-comment
    (let ((ret (us-analyze-comment x loc mod ialist walist warnings)))
      (implies (force (vl-wirealist-p walist))
               (vl-emodwirelist-p (mv-nth 1 ret))))))



(defsection us-analyze-commentmap

  (defund us-analyze-commentmap (x mod ialist walist warnings)
    "Returns (MV WARNINGS IGNORE-BITS)"
    (declare (xargs :guard (and (vl-commentmap-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod))
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil))
         ((cons loc str) (car x))
         ((mv warnings ignore-bits1) (us-analyze-comment str loc mod ialist walist warnings))
         ((mv warnings ignore-bits2) (us-analyze-commentmap (cdr x) mod ialist walist warnings)))
      (mv warnings (append ignore-bits1 ignore-bits2))))

  (local (in-theory (enable us-analyze-commentmap)))

  (defmvtypes us-analyze-commentmap (nil true-listp))

  (defthm vl-warninglist-p-of-us-analyze-commentmap
    (let ((ret (us-analyze-commentmap x mod ialist walist warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 ret)))))

  (defthm vl-emodwirelist-p-us-analyze-commentmap
    (let ((ret (us-analyze-commentmap x mod ialist walist warnings)))
      (implies (force (vl-wirealist-p walist))
               (vl-emodwirelist-p (mv-nth 1 ret))))))



