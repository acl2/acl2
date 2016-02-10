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
(include-book "utils")
(include-book "../../expr")
(include-book "../../mlib/expr-tools")
(local (include-book "../../util/arithmetic"))
(local (non-parallel-book))

(local (xdoc::set-default-parents parse-expressions))

(local (defthm nfix-of-len
         (equal (nfix (len x)) (len x))))

;; Dumb accumulated persistence hacking
(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ACL2::LEN-WHEN-PREFIXP
                           double-containment
                           acl2::consp-by-len
                           VL-WARNINGLIST-P-WHEN-NOT-CONSP
                           ACL2::PREFIXP-WHEN-EQUAL-LENGTHS
                           ACL2::SUBLISTP-WHEN-PREFIXP
                           ACL2::LOWER-BOUND-OF-LEN-WHEN-SUBLISTP
                           ACL2::INDEX-OF-<-LEN
                           default-<-1
                           default-<-2
                           ACL2::CANCEL_TIMES-EQUAL-CORRECT
                           ACL2::CANCEL_PLUS-EQUAL-CORRECT
                           VL-WARNINGLIST-P-WHEN-SUBSETP-EQUAL
                           VL-TOKENLIST-P-WHEN-SUBSETP-EQUAL
                           ACL2::LISTPOS-UPPER-BOUND-STRONG-2
                           VL-TOKENLIST-P-WHEN-MEMBER-EQUAL-OF-VL-TOKENLISTLIST-P
                           ACL2::ALISTP-OF-CDR
                           ACL2::CONSP-OF-CAR-WHEN-ALISTP
                           ALISTP-WHEN-ALL-HAVE-LEN
                           (tau-system)
                           nfix
                           ;(:rules-of-class :type-prescription :here)
                           (:t vl-warninglist-fix)
                           (:t vl-tokenlist-fix)
                           CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P
                           ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP
                           consp-when-member-equal-of-vl-usertypes-p
                           acl2::consp-when-member-equal-of-keyval-alist-p
                           (:t atom)
                           not
                           vl-expr-p-when-member-equal-of-vl-exprlist-p
                           acl2::keyval-alist-p
                           stringp-when-true-listp)))

(defines vl-expr-has-any-atts-p
  :short "Check whether an expression has any attributes."
  :long "<p>The parser uses this to ensure that we don't encounter any nested
attributes.</p>"

  :flag nil

  (define vl-expr-has-any-atts-p ((x vl-expr-p))
    :parents nil
    :returns (bool booleanp :rule-classes :type-prescription)
    :measure (vl-expr-count x)
    (b* (((when (vl-fast-atom-p x))
          nil)
         ((vl-nonatom x) x))
      (or (consp x.atts)
          (vl-exprlist-has-any-atts-p x.args))))

  (define vl-exprlist-has-any-atts-p ((x vl-exprlist-p))
    :parents nil
    :returns (bool booleanp :rule-classes :type-prescription)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (or (vl-expr-has-any-atts-p (car x))
          (vl-exprlist-has-any-atts-p (cdr x))))))



(define vl-parse-op-alist-p ((arity maybe-natp) x)
  (if (atom x)
      (not x)
    (and (consp (car x))
         (symbolp (caar x)) ;; token type to match
         (vl-op-p (cdar x))
         (eql arity (vl-op-arity (cdar x)))
         (vl-parse-op-alist-p arity (cdr x))))
  ///
  (defthm vl-parse-op-alist-p-when-atom
    (implies (atom x)
             (equal (vl-parse-op-alist-p arity x)
                    (not x))))
  (defthm vl-parse-op-alist-p-of-cons
    (equal (vl-parse-op-alist-p arity (cons a x))
           (and (consp a)
                (symbolp (car a))
                (vl-op-p (cdr a))
                (eql arity (vl-op-arity (cdr a)))
                (vl-parse-op-alist-p arity x)))))


(defparser vl-parse-op (arity alist)
  :short "Compatible with seq.  Match any of the tokens specified in this
alist, and return the corresponding @(see vl-op-p) for it."
  :long "<p>This helps to avoid many case splits throughout our operator
parsing functions.</p>"
  :guard (and (maybe-natp arity)
              (vl-parse-op-alist-p arity alist))
  :result (and (equal (vl-op-p val) (if val t nil))
                (equal (vl-op-arity val)
                       (if val arity (vl-op-arity nil))))
  :fails never
  :count strong-on-value
  :measure (len alist)
  :hint-chicken-switch t
  (seq tokstream
       (when (or (atom (vl-tokstream->tokens))
                 (atom alist))
         (return nil))
       (when (vl-is-token? (caar alist))
         (:= (vl-match))
         (return (cdar alist)))
       (return-raw
        (vl-parse-op arity (cdr alist))))
  ///
  (defthm vl-parse-op-when-atom
    (implies (atom (vl-tokstream->tokens))
             (not (mv-nth 1 (vl-parse-op arity alist)))))
  (defthm vl-parse-op-eof-helper
    (b* (((mv ?err ?val new-tokstream)
          (vl-parse-op arity alist :tokstream tokstream)))
      (implies (consp (vl-tokstream->tokens :tokstream new-tokstream))
               (consp (vl-tokstream->tokens))))
    :rule-classes ((:forward-chaining :trigger-terms ((vl-parse-op arity alist))))))



(in-theory (disable vl-parse-op-alist-p-when-atom
                    vl-parse-op-alist-p-of-cons))


(define vl-mixed-binop-list-p (x)
  :short "A list of alternating expressions, operators, and attributes."

  :long "<p>All of the binary operators in Verilog are left-associative, but it
is difficult to directly build a left-associative structure in straightforward
recursive descent parsing.</p>

<p>So instead, our expression parsers build <i>mixed binop lists</i> which we
then left-associate later.</p>

<p>Ignoring attributes for a moment, the idea is that these lists look like the
 following:</p>

@({
    (EXPR OP EXPR OP EXPR OP EXPR ... EXPR)
})

<p>So for instance, to parse the Verilog source code @('\"1 + 2 + 3 + 4\"'),
the plan is first to build a mixed list which looks like</p>

@({
    (1 + 2 + 3 + 4)
})

<p>and then to fully left-associate this list into the expected form,</p>

@({
    (+ (+ (+ 1 2) 3) 4)
})

<p>Attributes only make this slightly more complex.  The actual format of our
 mixed list is</p>

@({
    (EXPR OP ATTS EXPR OP ATTS ... EXPR)
})

<p>Where each ATTS belongs to the OP immediately preceeding it.</p>"

  (and (consp x)
       (vl-expr-p (car x))
       (or (not (consp (cdr x)))
           (and (consp (cddr x))
                (consp (cdddr x))
                (let ((op   (second x))
                      (atts (third x))
                      (rest (cdddr x)))
                  (and (vl-op-p op)
                       (equal (vl-op-arity op) 2)
                       (vl-atts-p atts)
                       (vl-mixed-binop-list-p rest))))))

  ///
  (defthm vl-mixed-binop-list-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-mixed-binop-list-p x)
                    nil)))

  (defthm vl-mixed-binop-list-p-of-singleton
    (equal (vl-mixed-binop-list-p (list x))
           (vl-expr-p x)))

  (defthm vl-mixed-binop-list-p-of-list*
    (equal (vl-mixed-binop-list-p (list* x y z w))
           (and (vl-expr-p x)
                (vl-op-p y)
                (equal (vl-op-arity y) 2)
                (vl-atts-p z)
                (vl-mixed-binop-list-p w)))))



(define vl-left-associate-mixed-binop-list ((x vl-mixed-binop-list-p))
  :returns (expr vl-expr-p :hyp :guard)
  :measure (len x)
  (if (consp (cdr x))
      (let ((e1      (first x))
            (op      (second x))
            (atts    (third x))
            (e2      (fourth x))
            (rest    (cddddr x)))
        ;; At each step, we just merge the first two expressions using the op
        ;; and attributes between them.
        (vl-left-associate-mixed-binop-list
         (cons (make-vl-nonatom :op op
                                :atts atts
                                :args (list e1 e2))
               rest)))
    (car x))
  :prepwork ((local (in-theory (enable vl-mixed-binop-list-p
                                       vl-arity-ok-p)))))



(define vl-build-indexing-nest ((expr vl-expr-p)
                                (indices vl-exprlist-p))
  :returns (expr vl-expr-p :hyp :fguard)
  :short "Build the proper expression for successive indexing operations."
  :long "<p>Another operation which we want to left-associate is bit/part
selection, which might also be called array or memory indexing.  The idea is
that for @('foo[1][2][3]'), we want to build an expression of the form:</p>

@({
     (vl-index (vl-index (vl-index foo 1)
                         2))
               3)
})

<p>This is easy because we are only dealing with one operation and no
attributes, so we can just read the list of selects and then left-associate
them.</p>"
  (if (atom indices)
      expr
    (vl-build-indexing-nest (make-vl-nonatom :op :vl-index
                                             :args (list expr (car indices)))
                            (cdr indices)))
  :prepwork ((local (in-theory (enable vl-arity-ok-p)))))


(defenum vl-erangetype-p
  (:vl-index ;; for bit selects or array indexes
   :vl-colon
   :vl-pluscolon
   :vl-minuscolon)
  :parents (vl-erange-p)
  :short "Type of an expression range.")

(deflist vl-erangetypelist-p (x)
  (vl-erangetype-p x)
  :elementp-of-nil nil
  ///
  (defthm vl-erangetype-p-of-vl-type-of-matched-token
    ;; ugly, but effective.
    (implies (vl-erangetypelist-p types)
             (equal (vl-erangetype-p (vl-type-of-matched-token types tokens))
                    (if (vl-type-of-matched-token types tokens)
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable vl-type-of-matched-token)))))

(defaggregate vl-erange
  ((type  vl-erangetype-p)
   (left  vl-expr-p)
   (right vl-expr-p))
  :tag :vl-erange
  :layout :fulltree
  :short "An <i>expression range</i> is a temporary internal representation of
the ranges for select-like expressions (bit selects, array indexes, part
selects, @('+:') and @('-:') expressions."
  :long "<p>For single-bit selects, we just set left and right to the same
expression.</p>")

(encapsulate
  ()
  (local (in-theory (enable vl-arity-ok-p)))
  (local (defthm not-vl-erange-p-when-invalid-type
           (implies (and (not (equal (vl-erange->type range) :vl-index))
                         (not (equal (vl-erange->type range) :vl-colon))
                         (not (equal (vl-erange->type range) :vl-pluscolon))
                         (not (equal (vl-erange->type range) :vl-minuscolon)))
                    (not (vl-erange-p range)))
           :hints(("Goal"
                   :in-theory (e/d (vl-erangetype-p)
                                   (return-type-of-vl-erange->type))
                   :use ((:instance return-type-of-vl-erange->type (x range)))))))

  (define vl-build-range-select ((expr vl-expr-p)
                                 (range vl-erange-p))
    :returns (expr[range] vl-expr-p :hyp :fguard)
    (b* (((vl-erange range) range))
      (case range.type
        (:vl-index
         (make-vl-nonatom :op :vl-index
                          :args (list expr range.left)))
        (:vl-colon
         (make-vl-nonatom :op :vl-select-colon
                          :args (list expr range.left range.right)))
        (:vl-pluscolon
         (make-vl-nonatom :op :vl-select-pluscolon
                          :args (list expr range.left range.right)))
        (:vl-minuscolon
         (make-vl-nonatom :op :vl-select-minuscolon
                          :args (list expr range.left range.right))))))

  (define vl-build-range-select-with ((expr vl-expr-p)
                                      (range vl-erange-p))
    :returns (expr-with-range vl-expr-p :hyp :fguard)
    (b* (((vl-erange range) range))
      (case range.type
        (:vl-index
         (make-vl-nonatom :op :vl-with-index
                          :args (list expr range.left)))
        (:vl-colon
         (make-vl-nonatom :op :vl-with-colon
                          :args (list expr range.left range.right)))
        (:vl-pluscolon
         (make-vl-nonatom :op :vl-with-pluscolon
                          :args (list expr range.left range.right)))
        (:vl-minuscolon
         (make-vl-nonatom :op :vl-with-minuscolon
                          :args (list expr range.left range.right)))))))



(define vl-make-guts-from-inttoken ((x vl-inttoken-p))
  :returns (guts vl-atomguts-p :hyp :fguard)
  (b* (((vl-inttoken x) x))
    (if x.value
        (make-vl-constint :origwidth  x.width
                          :origtype   (if x.signedp :vl-signed :vl-unsigned)
                          :value      x.value
                          :wasunsized x.wasunsized)
      (make-vl-weirdint :origwidth  x.width
                        :origtype   (if x.signedp :vl-signed :vl-unsigned)
                        :bits       x.bits
                        :wasunsized x.wasunsized))))


(define vl-mark-as-explicit-parens
  :short "Annotate an expression as having explicit parentheses."
  ((x vl-expr-p))
  :returns (new-x vl-expr-p :hyp :guard)

  :long "<p>For some kinds of linting checks, we may want to know whether the
original expression had any parens, e.g., we might want to warn the user if
they have typed</p>

@({
     a & b < c
})

<p>Because this gets parsed as @('a & (b < c)'), which seems strange and may
catch the user by surprise.  On the other hand, if they've typed</p>

@({
     a & (b < c)
})

<p>Then, as strange as this is, it seems to be what they want, and we probably
don't want to complain about it.</p>

<p>But these expressions will be identical after parsing unless we somehow
remember where explicit parens were.  To facilitate this, we set the
@('VL_EXPLICIT_PARENS') attribute on non-atoms that have explicit parens.</p>

<p>Note that we don't bother to set @('VL_EXPLICIT_PARENS') on atoms, e.g., the
following really are still parsed equivalently:</p>

@({
    (a) & b      vs.    a & b
})

<p>This is possibly unfortunate, but atoms don't have attributes so what else
would we do?</p>"

  (b* (((when (vl-fast-atom-p x))
        x)
       (atts (vl-nonatom->atts x))
       (atts (acons "VL_EXPLICIT_PARENS" nil atts)))
    (change-vl-nonatom x :atts atts)))

(defparser vl-maybe-parse-base-primary ()
  :parents (vl-parse-primary)
  :short "Match basic, atomic kinds of @('primary') expressions, such as
@('primary_literal'), @('this'), @('$'), and @('null'), returns a @(see
vl-expr-p)."

  :long "<p>In SystemVerilog-2012, we have:</p>

@({
     primary ::= primary_literal
               | 'this'
               | '$'
               | 'null'
               | ... other, more complex things ...

     primary_literal ::= number
                       | time_literal
                       | unbased_unsized_literal
                       | string_literal

     number ::= integral_number
              | real_number

     integral_number ::= decimal_number
                       | octal_number
                       | binary_number
                       | hex_number
})

<p>This is very similar to the @('primary') production in Verilog-2005:</p>

@({
     primary ::= number
               | string
               | ... other, more complex things ...

     number ::= decimal_number
              | octal_number
              | binary_number
              | hex_number
              | real_number
})

<p>We ignore the \"other, more complex things\" here, and just focus on the
simple primaries.  Aside from some minor lexical differences at the tips which
are handled by the @(see lexer) (see for instance @(see lex-strings) and @(see
lex-numbers)) the main difference here is that SystemVerilog adds time
literals, unbased unsized literals, @('this'), @('$'), and @('null').</p>"

  :result (vl-maybe-expr-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (seq tokstream
       (when (vl-is-token? :vl-inttoken)
         (int := (vl-match))
         (return (make-vl-atom :guts (vl-make-guts-from-inttoken int))))

       (when (vl-is-token? :vl-realtoken)
         (real := (vl-match))
         (return
          (b* ((value (vl-echarlist->string (vl-realtoken->etext real))))
            (make-vl-atom :guts (make-vl-real :value value)))))

       (when (vl-is-token? :vl-stringtoken)
         (str := (vl-match))
         (return
          (b* ((value (vl-stringtoken->expansion str)))
            (make-vl-atom :guts (make-vl-string :value value)))))

       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         ;; That's it for regular Verilog.
         (return nil))

       ;; New things for SystemVerilog-2012:
       (when (vl-is-token? :vl-extinttoken)
         (ext := (vl-match))
         (return
          (b* ((value (vl-extinttoken->value ext)))
            (make-vl-atom :guts (make-vl-extint :value value)))))

       (when (vl-is-token? :vl-timetoken)
         (time := (vl-match))
         (return
          (b* (((vl-timetoken time) time))
            (make-vl-atom :guts (make-vl-time :quantity time.quantity
                                              :units time.units)))))

       (when (vl-is-token? :vl-kwd-null)
         (:= (vl-match))
         (return (hons-copy (make-vl-atom
                             :guts (make-vl-keyguts :type :vl-null)))))

       (when (vl-is-token? :vl-kwd-default)
         (:= (vl-match))
         (return (hons-copy (make-vl-atom
                             :guts (make-vl-keyguts :type :vl-default)))))

       (when (vl-is-token? :vl-kwd-this)
         (:= (vl-match))
         (return (hons-copy (make-vl-atom
                             :guts (make-vl-keyguts :type :vl-this)))))

       (when (vl-is-token? :vl-$)
         (:= (vl-match))
         (return (hons-copy (make-vl-atom
                             :guts (make-vl-keyguts :type :vl-$)))))

       (return nil))
  ///
  (defthmd tokens-nonempty-when-vl-maybe-parse-base-primary
    (b* (((mv ?errmsg val ?new-tokstream)
          (vl-maybe-parse-base-primary)))
      (implies val (consp (vl-tokstream->tokens))))))



(defval *vl-very-simple-type-table*
  :parents (vl-parse-very-simple-type)
  :showval t
  (list
   (cons :vl-kwd-byte      (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-byte))))
   (cons :vl-kwd-shortint  (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-shortint))))
   (cons :vl-kwd-int       (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-int))))
   (cons :vl-kwd-longint   (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-longint))))
   (cons :vl-kwd-integer   (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-integer))))
   (cons :vl-kwd-time      (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-time))))
   (cons :vl-kwd-bit       (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-bit))))
   (cons :vl-kwd-logic     (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-logic))))
   (cons :vl-kwd-reg       (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-reg))))
   (cons :vl-kwd-shortreal (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-shortreal))))
   (cons :vl-kwd-real      (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-real))))
   (cons :vl-kwd-realtime  (hons-copy (make-vl-atom :guts (make-vl-basictype :kind :vl-realtime))))))

(defval *vl-very-simple-type-tokens*
  :parents (vl-parse-very-simple-type)
  :showval t
  (alist-keys *vl-very-simple-type-table*))

(defparser vl-parse-very-simple-type ()
  :short "Match the very simplest @('simple_type') keywords, return an
expression."

  :long "<p>The rule from SystemVerilog-2012 is:</p>

@({
     simple_type ::= integer_type
                   | non_integer_type
                   | ps_type_identifier
                   | ps_parameter_identifier
})

<p>This function matches only the first two variants, which are completely
trivial:</p>

@({
     integer_type ::= integer_vector_type | integer_atom_type

     integer_vector_type ::= 'bit' | 'logic' | 'reg'

     integer_atom_type   ::= 'byte' | 'shortint' | 'int'
                           | 'longint' | 'integer' | 'time'

     non_integer_type ::= 'shortreal' | 'real' | 'realtime'
})"
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (type := (vl-match-some-token *vl-very-simple-type-tokens*))
       (return (cdr (assoc (vl-token->type type)
                           *vl-very-simple-type-table*))))
  ///
  (defthm vl-parse-very-simple-type-when-eof
    (b* (((mv errmsg ?val ?new-tokstream)
          (vl-parse-very-simple-type)))
      (implies (atom (vl-tokstream->tokens))
               errmsg))))

(defparser vl-parse-parameter-value-assignment-hack ()
  :short "Ostensibly match a @('parameter_value_assignment') within an
expression."

  :long "<p>In Verilog-2005, parameter value assignments could only occur in
module instances (e.g., you might instantiate an adder with #(.width(16)) or
just #(16)).  But in SystemVerilog-2012, they can now be embedded within
certain kinds of casting and streaming concatenation expressions.</p>

<p>We don't see a very good way to support this in our current expression
format.  So, for now, if we actually encounter a parameter value assignment in
one of these contexts, we'll just cause a parse error.  If some day we actually
need to support this, we might be able to add some new kind of fancy
operator(s), e.g., a namedarg operator with an alternating list of name/value
expressions.</p>"
  :result (not val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-pound))
       (:= (vl-match-token :vl-lparen))
       (return-raw
        (vl-parse-error
         "Embedded parameter value assignments #(...) aren't implemented yet."))))

(defparser vl-parse-pva-tail ()
  :short "Match @(' { '::' identifier [parameter_value_assignment] } '::'
identifier ') and return an expression."

  :long "<p>Since we start by matching a @('::'), we always turn the
identifiers into hid pieces instead of ordinary id atoms.</p>

<p>We don't actually support parameter value assignments within expressions
yet; they'll just cause a parse error.</p>"

  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :verify-guards nil

  (seq tokstream
       (:= (vl-match-token :vl-scope))
       (head := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-pound)
         (:= (vl-parse-parameter-value-assignment-hack))
         (return-raw
          ;; Should never actually get here until we implement PVAs.
          (vl-parse-error "Implement PVAs.")))

       (unless (vl-is-token? :vl-scope)
         (return
          (make-vl-atom
           :guts (make-vl-hidpiece :name (vl-idtoken->name head)))))

       (tail := (vl-parse-pva-tail))
       (return
        (make-vl-nonatom
         :op :vl-scope
         :args (list (make-vl-atom
                      :guts (make-vl-hidpiece :name (vl-idtoken->name head)))
                     tail))))
  ///
  (verify-guards vl-parse-pva-tail-fn))

(defparser vl-parse-0+-scope-prefixes ()
  :short "Match @('{ id '::' }') and return an expression list with all of the
ids that have been matched."
  :long "<p>See also @(see vl-parse-indexed-id-2012) and @(see abstract-hids).
We use this in the tricky case of parsing:</p>

@({
      { id '::' } hierarchical_identifier select
})

<p>But per our desired abstract HID representation, we want to keep all of the
scoping stuff bundled up together, so we prefer to match it first, if it
exists.</p>"
  :verify-guards nil
  :result (vl-exprlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (seq tokstream
       (unless (and (vl-is-token? :vl-idtoken)
                    (vl-lookahead-is-token? :vl-scope (cdr (vl-tokstream->tokens))))
         (return nil))
       (first := (vl-match))
       (:= (vl-match))
       (rest := (vl-parse-0+-scope-prefixes))
       (return
        (cons (make-vl-atom :guts (make-vl-hidpiece :name (vl-idtoken->name first)))
              rest)))
  ///
  (verify-guards vl-parse-0+-scope-prefixes-fn
    :hints(("Goal" :in-theory (enable vl-lookahead-is-token?
                                      vl-is-token?
                                      vl-match))))

  (defthm vl-parse-0+-scope-prefixes-on-eof
    (implies (not (consp (vl-tokstream->tokens)))
             (b* (((mv & val new-tokstream) (vl-parse-0+-scope-prefixes)))
               (and (not val)
                    (not (consp (vl-tokstream->tokens :tokstream new-tokstream))))))))

(define vl-tack-scopes-onto-hid ((scopes vl-exprlist-p)
                                 (hid    vl-expr-p))
  :returns (expr vl-expr-p)
  (if (atom scopes)
      (vl-expr-fix hid)
    (make-vl-nonatom :op :vl-scope
                     :args (list (car scopes)
                                 (vl-tack-scopes-onto-hid (cdr scopes) hid)))))

;; For debugging you may want to comment out functions and add, as a temporary hack:
;; (set-bogus-mutual-recursion-ok t)


(defparsers parse-expressions
  :parents (parser)
  :short "Parser for Verilog and SystemVerilog expressions."

  :long "<p>This is very complicated because everything about expressions is
mutually recursive.  Most of the functions here correspond to particular
productions in the grammars of the Verilog-2005 or SystemVerilog-2012.  A
few high-level notes:</p>

<ul>

<li>The documentation for each function generally describes the grammar
productions that are being implemented.</li>

<li>We generally simplify the grammar rules by removing any bare \"aliases\"
such as @('base_expression ::= expression') and @('attr_name ::=
identifier').</li>

<li>We do not try to implement any separation between \"ordinary\" expressions
and \"constant\" expressions.  I think the whole treatment of constant
expressions as a syntactic construct is somewhat misguided.  It is difficult to
imagine truly handling constant expressions at parse time.  For instance, in a
parameterized module with, say, a @('width') parameter, you really want to
resolve expressions like @('width-1') into constants and treat them as constant
indexes.  But you can't do this until you know the values for these parameters,
which you don't know until you've read all the instances of the module,
etc.</li>

</ul>"
  :flag-local nil

  :hints(("Goal"
          :do-not-induct t
          :do-not '(generalize fertilize)))

  (defparser vl-parse-attr-spec ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match a single @('attr_spec'), return a singleton @(see vl-atts-p)."
    :long "<p>Verilog-2005 and SystemVerilog-2012 agree exactly about the
definition of @('attr_spec'):</p>

@({
attr_spec ::= attr_name [ '=' constant_expression ]
attr_name ::= identifier
})"
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :verify-guards nil
    (seq tokstream
          (id := (vl-match-token :vl-idtoken))
          (when (vl-is-token? :vl-equalsign)
            (:= (vl-match))
            (expr := (vl-parse-expression)))
          (when (and expr (vl-expr-has-any-atts-p expr))
            (return-raw
             (vl-parse-error "Nested attributes are illegal.")))
          (return (list (cons (vl-idtoken->name id) expr)))))

  (defparser vl-parse-attribute-instance-aux ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match @(' attr_spec { ',' attr_spec' } '), return a @(see vl-atts-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
          (first :s= (vl-parse-attr-spec))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match))
            (rest := (vl-parse-attribute-instance-aux)))
          (return (append first rest))))

  (defparser vl-parse-attribute-instance ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match (* ... *), return a @(see vl-atts-p)."
    :long "<p>Verilog-2005 and SystemVerilog-2012 agree exactly about the
definition of @('attribute_instance'):</p>

@({
    attribute_instance ::= '(*' attr_spec { ',' attr_spec } '*)'
})"
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    (seq tokstream
          (:= (vl-match-token :vl-beginattr))
          (data := (vl-parse-attribute-instance-aux))
          (:= (vl-match-token :vl-endattr))
          (return data)))

  (defparser vl-parse-0+-attribute-instances-aux ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match @('{ attribute_instance }'), collecting all attributes in
the order they were seen, without proper duplicity checking."
    :long "<p>We convert each individual @('attribute_instance') into an
@('vl-atts-p') alist, and then merge these together using @(see append), so
that for instance:</p>

@({
    (* foo *) (* bar *)
})

<p>Is treated in just the same way as:</p>

@({
     (* foo, bar *)
})"
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
          (when (not (vl-is-token? :vl-beginattr))
            (return nil))
          (first :s= (vl-parse-attribute-instance))
          (rest := (vl-parse-0+-attribute-instances-aux))
          (return (append first rest))))

  (defparser vl-parse-0+-attribute-instances ()
    :short "Top level parser for @('{ attribute_instance }') with proper
duplicity checking and warnings.  Returns a @(see vl-atts-p)."

    :long "<p>This is a wrapper.  Almost all of the work is done by the aux
function, @(see vl-parse-0+-attribute-instances-aux).  The aux function gathers
up an @(see vl-atts-p) that has all the attributes in the order they were seen
in.  For instance, it would produce:</p>

@({
       (* foo = 1 *)  (* bar = 2, foo = 2 *)
          --->
       (( \"foo\" . <1> )     ; Where <1> means, a proper vl-expr-p with
        ( \"bar\" . <2> )     ; the number 1.
        ( \"foo\" . <2> ))
})

<p>This isn't quite right.  We want any later attributes to shadow the previous
attributes, and we want to warn about any attributes like \"foo\" that occur
multiple times.  So, in this wrapper, we check for duplicates and issue
warnings, and we fix up the alists to get unique keys bound to the right
values.</p>"
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    (seq tokstream
          (when (not (vl-is-token? :vl-beginattr))
            ;; Stupid hack for performance.  Usually there are no attributes,
            ;; so we don't need to do anything more.
            (return nil))
          (loc := (vl-current-loc))
          (original-atts := (vl-parse-0+-attribute-instances-aux))
          (return-raw
           (b* ((atts
                 ;; The original-atts are in the order seen.
                 ;;  - Reversing them puts the later occurrences first, which
                 ;;    is good because these are the occurrences we want to keep
                 ;;  - Shrinking gets rid of any earlier occurrences, and also
                 ;;    re-reverses the list so we get them in the right order.
                 (fast-alist-free (hons-shrink-alist (rev original-atts) nil)))
                ((when (same-lengthp atts original-atts))
                 ;; No dupes, nothing to warn about
                 (mv nil atts tokstream))
                (w (make-vl-warning
                    :type :vl-warn-shadowed-atts
                    :msg "~l0: Found multiple occurrences of ~&1 in ~
                          attributes.  Later occurrences take precedence."
                    :args (list loc
                                (duplicated-members
                                 (alist-keys original-atts)))
                    :fatalp nil
                    :fn __function__))
                (tokstream (vl-tokstream-add-warning w)))
             (mv nil atts tokstream)))))


; system_function_call ::=
;    system_identifier [ '(' expression { ',' expression } ')' ]
;
; Strangely, system calls are not allowed to have attributes even though
; regular function calls are allowed to.

  (defparser vl-parse-1+-expressions-separated-by-commas ()
    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
          (first :s= (vl-parse-expression))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match))
            (rest := (vl-parse-1+-expressions-separated-by-commas)))
          (return (cons first rest))))

  (defparser vl-parse-1+-keyval-expression-pairs ()
    :measure (two-nats-measure (vl-tokstream-measure) 400)
    (seq tokstream
          (first :s= (vl-parse-expression))
          (:= (vl-match-token :vl-colon))
          (second :s= (vl-parse-expression))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match))
            (rest := (vl-parse-1+-keyval-expression-pairs)))
          (return (cons (make-vl-nonatom :op :vl-keyvalue :args (list first second))
                        rest))))


  (defparser vl-parse-system-function-call ()
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    (seq tokstream
          (fn := (vl-match-token :vl-sysidtoken))
          (when (vl-is-token? :vl-lparen)
            (:= (vl-match))
            (args := (vl-parse-1+-expressions-separated-by-commas))
            (:= (vl-match-token :vl-rparen)))
          (return
           (let ((fname (make-vl-sysfunname :name (vl-sysidtoken->name fn))))
             (make-vl-nonatom :op :vl-syscall
                              :args (cons (make-vl-atom :guts fname) args))))))


; Mintypmax and Assignment Expressions.
;
; In Verilog-2005 we have:
;
;    expression ::= primary | ...
;    primary    ::= '(' mintypmax_expression ')' | ...
;
;    mintypmax_expression ::= expression
;                           | expression ':' expression ':' expression
;
; In SystemVerilog, this gets more complicated because of assignment operators.
; The mintypmax expression is still the same, but we also get:
;
;   expression ::= primary
;                | '(' operator_assignment ')'
;                | ...
;
;   primary ::= '(' mintypmax_expression ')'
;
;   operator_assignment ::= variable_lvalue assignment_operator expression
;
;   assignment_operator ::= '=' | '+=' | '-=' | '*=' | '/=' | '%=' | '&='
;                         | '|=' | '^=' | '<<=' | '>>=' | '<<<=' | '>>>='
;
; The variable_lvalue form is really complicated and crazy and I'm just not
; going to try to implement it correctly.  Instead, I'm going to pretend
; that the operator_assignment rule is:
;
;    operator_assignment ::= expression assignment_operator expression
;
; From the perspective of expression, then, it'd be okay to treat the grammar
; as if it were:
;
;   expression ::= primary
;                | ...      ;; no assignment operator
;
;   primary ::= '(' mintypmax_expression ')'
;
;   mintypmax_expression ::= expression
;                          | expression ':' expression ':' expression
;                          | expression assignment_operator expression
;
; This is nice and simple, except that:
;
;   - It arguably makes parse-primary too permissive.  For instance, it's now
;     legal to do: (a = b) as a primary directly, whereas, per a strict reading
;     of the Verilog grammar, it maybe needs to be ((a = b)) in contexts where
;     a primary is expected.  This doesn't seem like a big deal at all.
;
;   - It makes mintypmax expressions too permissive.  These expressions are
;     occasionally used outside of expression parsing, in contexts like delays
;     and parameter assignments.  It does seem unfortunate to allow, e.g.,
;     submodule connections like .foo(a = b).
;
; On the other hand, it doesn't seem *that* bad.  Our increment-elim transform
; is pretty restrictive and isn't going to allow bad expressions in these
; places, so if we tolerate them when parsing, that doesn't seem horrible.
;
; For now, I'm just going to say this is all okay.  If at some point this
; bothers us and we decide the parser needs to be more restrictive, we can just
; add a flag here to say whether or not we want to permit assignment operators.
; That flag will have to work its way up through vl-parse-primary, as well.

  (defparser vl-parse-mintypmax-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
          (min :s= (vl-parse-expression))

          (when (vl-is-token? :vl-colon)
            (:= (vl-match))
            (typ :s= (vl-parse-expression))
            (:= (vl-match-token :vl-colon))
            (max := (vl-parse-expression))
            (return (make-vl-nonatom :op :vl-mintypmax
                                     :args (list min typ max))))

          (when (eq (vl-loadconfig->edition config) :verilog-2005)
            (return min))

          ;; Add assignment handling here.
          (op := (vl-parse-op 2 '((:vl-equalsign  . :vl-binary-assign)        ; a = b
                                  (:vl-pluseq     . :vl-binary-plusassign)    ; (a += b)
                                  (:vl-minuseq    . :vl-binary-minusassign)   ; (a -= b)
                                  (:vl-timeseq    . :vl-binary-timesassign)   ; (a *= b)
                                  (:vl-diveq      . :vl-binary-divassign)     ; (a /= b)
                                  (:vl-remeq      . :vl-binary-remassign)     ; (a %= b)
                                  (:vl-andeq      . :vl-binary-andassign)     ; (a &= b)
                                  (:vl-oreq       . :vl-binary-orassign)      ; (a |= b)
                                  (:vl-xoreq      . :vl-binary-xorassign)     ; (a ^= b)
                                  (:vl-shleq      . :vl-binary-shlassign)     ; (a <<= b)
                                  (:vl-shreq      . :vl-binary-shrassign)     ; (a >>= b)
                                  (:vl-ashleq     . :vl-binary-ashlassign)    ; (a <<<= b)
                                  (:vl-ashreq     . :vl-binary-ashrassign)))) ; (a >>>= b)
          (unless op
            (return min))

          (rhs := (vl-parse-expression))
          (return (make-vl-nonatom :op op
                                   :args (list min rhs)))))


  (defparser vl-parse-range-expression ()
    :short "Match @('range_expression'), returning an @(see vl-erange-p)."
    :long "<p>In Verilog-2005 the rule boils down to:</p>

@({
    range_expression ::= expression
                       | expression ':' expression
                       | expression '+:' expression
                       | expression '-:' expression
})

<p>In SystemVerilog-2012 the rule is identical, but just split up across
several additional productions.</p>

@({
    range_expression ::= expression | part_select_range

    part_select_range ::= constant_range | indexed_range

    constant_range ::= expression ':' expression

    indexed_range ::= expression '+:' expression
                    | expression '-:' expression
})"

    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
          (e1 :s= (vl-parse-expression))
          (unless (vl-is-some-token? '(:vl-colon :vl-pluscolon :vl-minuscolon))
            (return (vl-erange :vl-index e1 e1)))
          (sep := (vl-match))
          (e2 := (vl-parse-expression))
          (return (vl-erange (vl-token->type sep) e1 e2))))


  (defparser vl-parse-concatenation ()
    :short "Match @(' concatenation ::= '{' expression { ',' expression } '}'')
and return a single @(':vl-concat') expression."

    :long "<p>Both Verilog-2005 and SystemVerilog-2012 agree exactly on the
syntax of a concatenation.</p>"
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    (seq tokstream
          (:= (vl-match-token :vl-lcurly))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rcurly))
          (return (make-vl-nonatom :op :vl-concat :args args))))


  (defparser vl-parse-stream-expression ()
    :short "Match stream_expression, returning a single expression."
    :long "<p>The SystemVerilog-2012 rule is:</p>
@({
     stream_expression ::= expression [ 'with' '[' array_range_expression ']' ]
})

<p>Where @('array_range_expression') is identical to
@('range_expression').</p>"

    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
          (expr :s= (vl-parse-expression))
          (unless (vl-is-token? :vl-kwd-with)
            (return expr))
          (:= (vl-match))
          (:= (vl-match-token :vl-lbrack))
          (range := (vl-parse-range-expression))
          (:= (vl-match-token :vl-rbrack))
          (return (vl-build-range-select-with expr range))))

  (defparser vl-parse-1+-stream-expressions-separated-by-commas ()
    :short "Match at least one (but perhaps more) stream expressions, return them
            as an expression list."
    :measure (two-nats-measure (vl-tokstream-measure) 320)
    (seq tokstream
          (first :s= (vl-parse-stream-expression))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match))
            (rest := (vl-parse-1+-stream-expressions-separated-by-commas)))
          (return (cons first rest))))

  (defparser vl-parse-stream-concatenation ()
    :short "Match stream_concatenation, return an expression list."
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    (seq tokstream
          (:= (vl-match-token :vl-lcurly))
          (args := (vl-parse-1+-stream-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rcurly))
          (return args)))

  (defparser vl-parse-simple-type ()
    :short "Match @('simple_type') and return an expression."
    :long "<p>The rule from SystemVerilog-2012 is:</p>

@({
     simple_type ::= integer_type
                   | non_integer_type
                   | ps_type_identifier
                   | ps_parameter_identifier
})

<p>The first two variants are simple and need not be part of the mutual
recursion; see @(see vl-parse-very-simple-type).  The other two variants
are somewhat horribly complex and redundant with one another.  After working
with these grammar rules, I believe simple_type is equivalent to:</p>

@({
   very_simple_type ::= integer_type | non_integer_type

   pva_tail ::=  { '::' identifier [ pva ] } '::' identifier

   simple_type ::=
        very_simple_type
      | 'local'    '::' identifier
      | '$unit'    pva_tail
      | identifier
      | identifier [ pva ] pva_tail
      | identifier { [ '[' expression ']' ] '.' identifier }
})"
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream

          (when (vl-is-token? :vl-kwd-local)
            ;; 'local' '::' identifier
            (:= (vl-match))
            (:= (vl-match-token :vl-scope))
            (tail := (vl-match-token :vl-idtoken))
            (return
             (make-vl-nonatom
              :op :vl-scope
              :args (list (make-vl-atom :guts (make-vl-keyguts :type :vl-local))
                          (make-vl-atom :guts (make-vl-hidpiece :name (vl-idtoken->name tail)))))))

          (when (vl-is-token? :vl-$unit)
            ;; '$unit' pva_tail
            (:= (vl-match))
            (tail := (vl-parse-pva-tail))
            (return
             (make-vl-nonatom
              :op :vl-scope
              :args (list (make-vl-atom :guts (make-vl-keyguts :type :vl-$unit))
                          tail))))

          (unless (vl-is-token? :vl-idtoken)
            (return-raw (vl-parse-very-simple-type)))

          (when (vl-lookahead-is-token? :vl-pound (cdr (vl-tokstream->tokens)))
            ;; identifier pva pva_tail
            (:= (vl-match))
            (:= (vl-parse-parameter-value-assignment-hack))
            (return-raw
             (vl-parse-error "Implement PVAs.")))

          (when (vl-lookahead-is-token? :vl-scope (cdr (vl-tokstream->tokens)))
            ;; identifier [pva] pva_tail with no pva
            (head := (vl-match))
            (tail := (vl-parse-pva-tail))
            (return
             (make-vl-nonatom
              :op :vl-scope
              :args (list (make-vl-atom :guts (make-vl-hidpiece
                                               :name (vl-idtoken->name head)))
                          tail))))

          ;; identifier | identifier { [ '[' expression ']' ] '.' identifier }
          ;; This is equivalent to hierarchical_identifier, except that we
          ;; can't have $root.  But we don't have to worry about that because
          ;; we know we have an ID, so it can't be root.
          (id := (vl-parse-hierarchical-identifier nil))
          (when (and (vl-idexpr-p id)
                     (not (vl-parsestate-is-user-defined-type-p (vl-idexpr->name id)
                                                                (vl-tokstream->pstate))))
            (return-raw
             (vl-parse-error (cat "Not a known type: " (vl-idexpr->name id)))))
          (return id)))


  (defparser vl-parse-slice-size ()
    :short "Match @(' slice_size ::= simple_type | expression ') and return it as
an expression."
    :long "<p>This matches the @('slice_size') production for SystemVerilog-2012,
which are used streaming concatenations.</p>

@({
     slice_size ::= simple_type | expression
})"

    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (b* ((backup (vl-tokstream-save))
         ((mv err expr tokstream) (vl-parse-simple-type))
         ((unless err)
          (mv err expr tokstream))
         (tokstream (vl-tokstream-restore backup)))
      (vl-parse-expression)))

  (defparser vl-parse-any-sort-of-concatenation ()
    :short "Match single, multiple, or streaming concatenations, or empty
queues."
    :long "<p>Both Verilog-2005 and SystemVerilog-2012 agree on the syntax for
concatenations and multiple concatenations:</p>

@({
     concatenation ::= '{' expression { ',' expression } '}'

     multiple_concatenation ::= '{' expression concatenation '}'
})

<p>By itself this is slightly tricky to parse: we don't know which production
we're matching until we have read the initial @(' '{' expression ').  If we
then find a comma, or a closing brace, we know it is a single concatenation.
Otherwise, if we find an opening brace, we know it is a multiple
concatenation.</p>

<p>SystemVerilog-2012 complicates this by adding streaming concatenations:</p>

@({
     streaming_concatenation ::=
       '{' stream_operator [slice_size] stream_concatenation '}'

     stream_operator ::= '>>' | '<<'
})

<p>Fortunately, streaming concatenations are easy to identify because they
always start with one of these @('stream_operators').</p>

<p>SystemVerilog also adds empty queues which are easy to identify:</p>

@({
     empty_queue ::= '{' '}'
})"

    :measure (two-nats-measure (vl-tokstream-measure) 0)
    (seq tokstream
          (:= (vl-match-token :vl-lcurly))

          (when (and (vl-is-token? :vl-rcurly) ;; {}
                     (not (eq (vl-loadconfig->edition config) :verilog-2005)))
            (:= (vl-match))
            (return (make-vl-atom :guts (make-vl-keyguts :type :vl-emptyqueue))))

          (when (and (vl-is-some-token? '(:vl-shl :vl-shr))
                     (not (eq (vl-loadconfig->edition config) :verilog-2005)))
            (op := (vl-match))
            (unless (vl-is-token? :vl-lcurly)
              (slicesize :s= (vl-parse-slice-size)))
            (args := (vl-parse-stream-concatenation))
            (:= (vl-match-token :vl-rcurly))
            (return
             (b* ((dir (vl-token->type op))
                  ((unless slicesize)
                   (make-vl-nonatom :op (if (eq dir :vl-shl)
                                            :vl-stream-left
                                          :vl-stream-right)
                                    :args args)))
               (make-vl-nonatom :op (if (eq dir :vl-shl)
                                        :vl-stream-left-sized
                                      :vl-stream-right-sized)
                                :args (cons slicesize args)))))

          (e1 :s= (vl-parse-expression))

          (when (vl-is-token? :vl-lcurly)
            ;; A multiple concatenation
            (concat := (vl-parse-concatenation))
            (:= (vl-match-token :vl-rcurly))
            (return (make-vl-nonatom :op :vl-multiconcat
                                     :args (list e1 concat))))

          ;; Otherwise, a regular concat -- does it have extra args?
          (when (vl-is-token? :vl-comma)
            (:= (vl-match))
            (rest := (vl-parse-1+-expressions-separated-by-commas))
            (:= (vl-match-token :vl-rcurly))
            (return (make-vl-nonatom :op :vl-concat
                                     :args (cons e1 rest))))

          ;; Nope, just a concat of one expression.
          (:= (vl-match-token :vl-rcurly))
          (return (make-vl-nonatom :op :vl-concat
                                   :args (list e1)))))




  (defparser vl-parse-hierarchical-identifier (recursivep)
    :short "Match a @('hierarchical_identifier')."
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :long "<p>In Verilog-2005, the rule is:</p>

@({
 hierarchical_identifier ::=
   { identifier [ '[' expression ']' '.' } identifier
})

<p>This permits, e.g., @('foo.bar[2].baz'), but at most one indexing expression
is allowed at each level, e.g., @('foo.bar[2][3].baz') is not allowed.</p>

<p>SystemVerilog extends this in two ways.  The new rule is:</p>

@({
    hierarchical_identifier ::=
      [ '$root' '.' ] { identifier bit_select '.' } identifier

    bit_select ::= { '[' expression ']' }
})

<p>The first extension, @('$root'), is straightforward enough.</p>

<p>The second extension is that there can now be multiple levels of indexing,
because the @('bit_select') production has any amount of replication allowed.
So, a hierarchical identifier such as @('foo.bar[2][3].baz') is now
permitted.</p>

<p>This function can return a hierarchical identifier or a simple identifier
expression.  The recursivep argument is used to determine, in the base case,
whether the atom we build should be a hidpiece or an ordinary id.  Basically,
if we have not yet seen a dot then recursivep is nil and we want to just build
a regular id token.  But otherwise, this id is just part of a hierarchical
identifier, so we convert it into a hidpiece.</p>"

    (b* ((sys-p (not (eq (vl-loadconfig->edition config) :verilog-2005))))
      (seq tokstream

            (when (and sys-p
                       (not recursivep)
                       (vl-is-token? :vl-$root))
              (:= (vl-match))
              (:= (vl-match-token :vl-dot))
              (tail := (vl-parse-hierarchical-identifier t))
              (return
               (b* ((guts (make-vl-keyguts :type :vl-$root))
                    (head (make-vl-atom :guts guts)))
                 (make-vl-nonatom :op :vl-hid-dot
                                  :args (list head tail)))))

            (id := (vl-match-token :vl-idtoken))

            (when (vl-parsestate-is-user-defined-type-p (vl-idtoken->name id)
                                                        (vl-tokstream->pstate))
              (return (make-vl-atom :guts (make-vl-typename
                                           :name (vl-idtoken->name id)))))

            (when (vl-is-token? :vl-dot)
              (:= (vl-match))
              (tail :s= (vl-parse-hierarchical-identifier t))
              (return
               (b* ((guts (make-vl-hidpiece :name (vl-idtoken->name id)))
                    (head (make-vl-atom :guts guts)))
                 (make-vl-nonatom :op :vl-hid-dot
                                  :args (list head tail)))))

            (unless sys-p
              ;; For Verilog-2005: match a single bracketed expression and only
              ;; if it is followed by a dot.

              (when (vl-is-token? :vl-lbrack)
                (expr := (b* ((backup (vl-tokstream-save))
                              ((mv err expr tokstream)
                               (seq tokstream
                                    (:= (vl-match))
                                    (expr :s= (vl-parse-expression))
                                    (:= (vl-match-token :vl-rbrack))
                                    (:= (vl-match-token :vl-dot))
                                    (return expr)))
                              ((unless err)
                               (mv nil expr tokstream))
                              (tokstream (vl-tokstream-restore backup)))
                           ;; Suppress the error, the [ may just not belong
                           ;; to us.
                           (mv nil nil tokstream))))

              (when expr
                ;; Found [expr] and a dot, so we should have a tail, too.
                (tail := (vl-parse-hierarchical-identifier t))
                (return
                 (b* ((from-guts (make-vl-hidpiece :name (vl-idtoken->name id)))
                      (from-expr (make-vl-atom     :guts from-guts))
                      (sel-expr  (make-vl-nonatom  :op :vl-index
                                                   :args (list from-expr expr))))
                   (make-vl-nonatom :op :vl-hid-dot
                                    :args (list sel-expr tail)))))

              ;; Else, found some stray bracket but not a good expr part.
              (return (make-vl-atom
                       :guts (if recursivep
                                 (make-vl-hidpiece :name (vl-idtoken->name id))
                               (make-vl-id :name (vl-idtoken->name id))))))

            ;; For SystemVerilog we can match any number of bracketed exprs
            ;; here, but again only if they're followed by a dot.
            (when (vl-is-token? :vl-lbrack)
              (exprs :w= (b* ((backup (vl-tokstream-save))
                              ((mv err exprs tokstream)
                               (seq tokstream
                                    (exprs := (vl-parse-0+-bracketed-expressions))
                                    (:= (vl-match-token :vl-dot))
                                    (return exprs)))
                              ((unless err)
                               (mv nil exprs tokstream))
                              (tokstream (vl-tokstream-restore backup)))
                           ;; Suppress the error, the [ may just not belong to
                           ;; us.
                           (mv nil nil tokstream))))

            (when exprs
              ;; Found [expr][expr][expr] and a dot, so we should have a tail
              (tail := (vl-parse-hierarchical-identifier t))
              (return
               (b* ((from-guts (make-vl-hidpiece :name (vl-idtoken->name id)))
                    (from-expr (make-vl-atom     :guts from-guts))
                    (sel-expr  (vl-build-indexing-nest from-expr exprs)))
                 (make-vl-nonatom :op :vl-hid-dot
                                  :args (list sel-expr tail)))))

            ;; Else, found some stray bracket that isn't ours
            (return
             (make-vl-atom
              :guts (if recursivep
                        (make-vl-hidpiece :name (vl-idtoken->name id))
                      (make-vl-id :name (vl-idtoken->name id))))))))

; function_call ::=
;    hierarchical_identifier { attribute_instance }
;      '(' expression { ',' expression } ')'

  (defparser vl-parse-function-call ()
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
          (id :s= (vl-parse-hierarchical-identifier nil))
          (atts :w= (vl-parse-0+-attribute-instances))
          (:= (vl-match-token :vl-lparen))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rparen))
          (return (cond ((and (vl-fast-atom-p id)
                              (vl-fast-id-p (vl-atom->guts id)))
                         ;; The function's name is a non-hierarchical identifier.  We
                         ;; convert it into a funname atom, instead, so that there is
                         ;; no confusion that it is not a variable.
                         (let ((fname (make-vl-funname
                                       :name (vl-id->name (vl-atom->guts id)))))
                           (make-vl-nonatom :op :vl-funcall
                                            :atts atts
                                            :args (cons (make-vl-atom :guts fname) args))))
                        (t
                         ;; Otherwise, a hierarchical identifier.  We just use it as is.
                         (make-vl-nonatom :op :vl-funcall
                                          :atts atts
                                          :args (cons id args)))))))




; primary ::=
;    number
;  | hierarchical_identifier [ { '[' expression ']' } '[' range_expression ']' ]
;  | concatenation
;  | multiple_concatenation
;  | function_call
;  | system_function_call
;  | '(' mintypmax_expression ')'
;  | string

  (defparser vl-parse-0+-bracketed-expressions ()
    :short "Match @('{ '[' expression ']') }'), return an expression list."
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (b* (((unless (vl-is-token? :vl-lbrack))
          ;; For termination, this needs to be a ruler.
          (mv nil nil tokstream))

         (backup (vl-tokstream-save))
         ((mv err first tokstream)
          (seq tokstream
                (:= (vl-match))
                (expr := (vl-parse-expression))
                (:= (vl-match-token :vl-rbrack))
                (return expr)))

         ((when (or err (not first)))
          ;; No initial expression; okay.  Restore the backup and return.
          (b* ((tokstream (vl-tokstream-restore backup)))
            (mv nil nil tokstream)))

         ((unless (mbt (< (vl-tokstream-measure)
                          (len (vl-tokstream-backup->tokens backup)))))
          (raise "termination failure")
          (vl-parse-error "termination failure"))

         ((mv erp rest tokstream) (vl-parse-0+-bracketed-expressions))
         ((when erp)
          (mv erp rest tokstream)))
      (mv nil (cons first rest) tokstream)))

  (defparser vl-parse-indexed-id-2005 (scopes recursivep)
    ;; This is for:
    ;;   hierarchical_identifier [ { '[' expression ']' } '[' range_expression ']' ]
    ;;
    ;; SCOPES is passed in from the outside.  It is NIL if there is no scope
    ;; part of the expression, or is a (possibly nested) scope expression to be
    ;; tacked onto the HID part.
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    :guard (vl-exprlist-p scopes)
    (seq tokstream
          (hid :s= (vl-parse-hierarchical-identifier recursivep))
          (bexprs :w= (vl-parse-0+-bracketed-expressions))
          (when (vl-is-token? :vl-lbrack)
            (:= (vl-match))
            (range := (vl-parse-range-expression))
            (:= (vl-match-token :vl-rbrack)))
          (return
           (let* ((ans (vl-tack-scopes-onto-hid scopes hid))
                  (ans (vl-build-indexing-nest ans bexprs)))
             (if range
                 (vl-build-range-select ans range)
               ans)))))

  (defparser vl-parse-indexed-id-2012 ()
    :measure (two-nats-measure (vl-tokstream-measure) 12)
    ;; This is for [ class_qualifier | package_scope ] hierarchical_identifier select
    ;; Support is somewhat partial right now...

    (seq tokstream
         (when (vl-is-some-token? '(:vl-kwd-local :vl-$unit))
           (first := (vl-match))
           (:= (vl-match-token :vl-scope))
           (morescopes := (vl-parse-0+-scope-prefixes))
           (return-raw
            (vl-parse-indexed-id-2005 (cons (case (vl-token->type first)
                                              (:vl-kwd-local (make-vl-atom :guts (make-vl-keyguts :type :vl-local)))
                                              (:vl-$unit     (make-vl-atom :guts (make-vl-keyguts :type :vl-$unit))))
                                            morescopes)
                                      t)))
         (scopes := (vl-parse-0+-scope-prefixes))
         (return-raw
          (vl-parse-indexed-id-2005 scopes (consp scopes)))))

  (defparser vl-parse-indexed-id ()
    :measure (two-nats-measure (vl-tokstream-measure) 13)
    (if (eq (vl-loadconfig->edition config) :verilog-2005)
        (vl-parse-indexed-id-2005 nil nil)
      (vl-parse-indexed-id-2012)))

  (defparser vl-parse-assignment-pattern ()
    :measure (two-nats-measure (vl-tokstream-measure) 500)
    (declare (xargs :measure-debug t))
    ;; We've parsed the initial '{ and need to figure out which form it is.  To
    ;; do that, we parse one expression, then check whether we have:
    ;;  rcurly -> positional pattern (with only 1 elt)
    ;;  comma -> positional pattern
    ;;  colon -> key/value pattern
    ;;  lcurly -> multiconcat pattern.
    (seq tokstream
         (first :s= (vl-parse-expression))
         (when (vl-is-token? :vl-rcurly)
           (:= (vl-match))
           (return (make-vl-nonatom :op :vl-pattern-positional :args (list first))))
         (when (vl-is-token? :vl-comma)
           ;; positional
           (:= (vl-match))
           (rest := (vl-parse-1+-expressions-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-nonatom :op :vl-pattern-positional
                                    :args (cons first rest))))

         (when (vl-is-token? :vl-colon)
           ;; key/val
           (:= (vl-match))
           (firstval :s= (vl-parse-expression))
           (when (vl-is-token? :vl-rcurly)
             (:= (vl-match))
             ;; just one key/val pair
             (return (make-vl-nonatom :op :vl-pattern-keyvalue
                                      :args (list (make-vl-nonatom
                                                   :op :vl-keyvalue
                                                   :args (list first firstval))))))
           ;; otherwise, better be a comma and then more key/values
           (:= (vl-match-token :vl-comma))
           (rest := (vl-parse-1+-keyval-expression-pairs))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-nonatom :op :vl-pattern-keyvalue
                                    :args (cons (make-vl-nonatom :op :vl-keyvalue
                                                                 :args (list first firstval))
                                                rest))))

         ;; Otherwise, better be an lcurly, and we have a multiconcat.
         (concat := (vl-parse-concatenation))
         (:= (vl-match-token :vl-rcurly))

         (return (make-vl-nonatom
                  :op :vl-pattern-multi
                  :args (list first concat)))))


  (defparser vl-parse-primary-main ()
    :measure (two-nats-measure (vl-tokstream-measure) 25)
    ;; This handles most primaries, but does not deal with casting.
    (b* ((backup (vl-tokstream-save))

         ((mv errmsg? expr tokstream)
          ;; Base primary handles things like numbers, 'this', 'null', '$'.
          ;; It doesn't deal with identifiers (which might be followed by dots/scopes)
          ;; It doens't match anything that can be used in a cast.
          (vl-maybe-parse-base-primary))

         ((when (or errmsg? ;; BOZO it never fails, so this could perhaps be simplified to just expr.
                    expr))
          (mv errmsg? expr tokstream))

         (tokstream (vl-tokstream-restore backup))

         ;; BOZO this isn't really finished at all, yet.

         (tokens (vl-tokstream->tokens))
         ((when (atom tokens))
          (vl-parse-error "Unexpected EOF."))

         (type (vl-token->type (car tokens)))
         ((when (or (eq type :vl-idtoken)
                    (eq type :vl-$root)
                    (eq type :vl-$unit)
                    (eq type :vl-kwd-local)))
          ;; Its either an hindex or a function call.  We need to check for
          ;; function call first, since, e.g.,our hindex would accept just the
          ;; hierarchical identifier, "foo", if given "foo(x, y, z)."
          (b* (;; Subtle: our backup is still valid
               ((mv err funcall tokstream) (vl-parse-function-call))
               ((unless err)
                (mv err funcall tokstream))
               (tokstream (vl-tokstream-restore backup)))
            (vl-parse-indexed-id)))

         ((when (eq type :vl-lcurly))
          ;; Concatenation, multiple concatenation, streaming concatenation,
          ;; or empty queue
          (vl-parse-any-sort-of-concatenation))

         ((when (eq type :vl-sysidtoken))
          ;; It can only be a system function call.
          (vl-parse-system-function-call))

         ((when (eq type :vl-lparen))
          ;; '(' mintypmax_expression ')'
          (seq tokstream
                (:= (vl-match))
                (expr := (vl-parse-mintypmax-expression))
                (:= (vl-match-token :vl-rparen))
                (return (vl-mark-as-explicit-parens expr))))

         ((when (eq type :vl-quote))
          (seq tokstream
               (:= (vl-match))
               (:= (vl-match-token :vl-lcurly))
               ;; Assignment pattern with no type cast.
               (return-raw (vl-parse-assignment-pattern)))))

      (vl-parse-error "Failed to match a primary expression.")))


  (defparser vl-parse-primary-cast ()
    :measure (two-nats-measure (vl-tokstream-measure) 30)
    ;; SystemVerilog Only.
    ;;
    ;; Matches main (cast-free) primaries and also primaries with casts.
    ;;
    ;; primary ::= cast | ...
    ;; cast ::= casting_type ''' '(' expression ')'       // <--- ''' is literally a quote mark
    ;; casting_type ::= ... | constant_primary | ...
    ;;
    ;; Arguably we should be able to do, e.g., "unsigned ' (-2'sd1) ' (1'bx);"
    ;; and in fact both NCVerilog and VCS seem to allow this.  But this makes
    ;; no sense and causes problems for termination, so, we'll insist that the
    ;; left-hand side of a cast is not itself a cast.
    (seq tokstream
          (primary :s= (vl-parse-primary-main))
          (when (vl-is-token? :vl-quote)
            (:= (vl-match))
            (when (vl-is-token? :vl-lparen)
              ;; Cast expression.
              (:= (vl-match))
              (arg := (vl-parse-expression))
              (:= (vl-match-token :vl-rparen))
              (return (make-vl-nonatom :op :vl-binary-cast :args (list primary arg))))
            ;; otherwise, better be a typed assignment pattern:
            (:= (vl-match-token :vl-lcurly))
            (pattern := (vl-parse-assignment-pattern))
            (return (make-vl-nonatom :op :vl-pattern-type :args (list primary pattern))))
          ;; Primary but not a cast.  Good enough.
          (return primary)))

  (defparser vl-parse-nonprimary-cast ()
    :measure (two-nats-measure (vl-tokstream-measure) 30)
    ;; SystemVerilog Only.
    ;;
    ;; The other (non-primary) casting types are:
    ;;   simple_type, 'signed', 'unsigned', 'string', 'const'
    (seq tokstream
          (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned :vl-kwd-string :vl-kwd-const))
            (type := (vl-match))
            (:= (vl-match-token :vl-quote))
            (:= (vl-match-token :vl-lparen))
            (arg := (vl-parse-expression))
            (:= (vl-match-token :vl-rparen))
            (return
             (b* ((casting-type (case (vl-token->type type)
                                  (:vl-kwd-signed   :vl-signed)
                                  (:vl-kwd-unsigned :vl-unsigned)
                                  (:vl-kwd-string   :vl-string)
                                  (:vl-kwd-const    :vl-const)))
                  (type-atom (make-vl-atom :guts (make-vl-basictype :kind casting-type))))
               (make-vl-nonatom :op :vl-binary-cast
                                :args (list type-atom arg)))))

          ;; Otherwise, better be a simple-type.
          (type :s= (vl-parse-simple-type))
          (:= (vl-match-token :vl-quote))
          (:= (vl-match-token :vl-lparen))
          (arg := (vl-parse-expression))
          (:= (vl-match-token :vl-rparen))
          (return (make-vl-nonatom :op :vl-binary-cast
                                   :args (list type arg)))))

 (defparser vl-parse-primary ()
    :measure (two-nats-measure (vl-tokstream-measure) 40)
    ;; Deals with casting and also other primaries.
    (b* (((when (eq (vl-loadconfig->edition config) :verilog-2005))
          (vl-parse-primary-main))

         ;; Try to parse basic primaries with or without casts
         (backup (vl-tokstream-save))
         ((mv errmsg expr tokstream) (vl-parse-primary-cast))
         ((unless errmsg)
          (mv errmsg expr tokstream))
         (tokstream (vl-tokstream-restore backup))

         ;; Try to parse other kinds of casts
         ((mv errmsg expr tokstream) (vl-parse-nonprimary-cast))
         ((unless errmsg)
          (mv errmsg expr tokstream))
         (tokstream (vl-tokstream-restore backup)))

      (vl-parse-error "Failed to match a primary expression.")))


; Definitions from Verilog-2005:
;
; expression ::=
;    primary
;  | unary_operator { attribute_instance } primary
;  | expression binary_operator { attribute_instance } expression
;  | conditional_expression
;
; conditional_expression ::=
;    expression '?' { attribute_instance } expression ':' expression
;
; Note also the precedence rules from Page 44.
;
;               Table 5-4 --- Precedence rules for operators
;
;   Highest Precedence      +  -  !  ~  &  ~&  |  ~|  ^  ~^  ^~    (unary)
;                           **
;                           *  /  %
;                           +  -               (binary)
;                           <<  >>  <<<  >>>
;                           <   <=  >    >=
;                           ==  !=  ===  !==
;                           &                  (binary)
;                           ^  ^~  ~^          (binary)
;                           |                  (binary)
;                           &&
;                           ||
;                           ?:                 (conditional operator)
;   Lowest Precedence       {} {{}}            (concatenations)
;
; And note also the associativity rule from 5.1.2. all operators shall
; associate left to right with the exception of the conditional operator, which
; shall associate right to left.
;
; SystemVerilog-2012 adds a few operators.  Note also that its new -> and <->
; operators are right associative.
;
; Just to refresh our memory, this is how we might write a grammar where '*' is
; to have higher precedence than '-':
;
;    expr ::= term { '-' term }
;    term ::= number { '*' number }
;
; In other words, the higher precedence an operator is, the closer to "number"
; it should occur.  Incorporating these precedence rules into the grammar, we
; come up with the following, new definition for expression:
;
; unary_expression ::=
;    unary_operator { attribute_instance } primary
;  | primary
;
; power_expression ::=
;    unary_expression { '**' { attribute_instance } unary_expression }
;
; mult_op ::= '*' | '/' | '%'
; mult_expression ::=
;    power_expression { mult_op { attribute_instance } power_expression }
;
; add_op ::= '+' | '-'
; add_expression ::=
;    mult_expression { add_op { attribute_instance } mult_expression }
;
; shift_op ::= '<<' | '>>' | '<<<' | '>>>'
; shift_expression ::=
;    add_expression { shift_op { attribute_instance } add_expression }
;
; compare_op ::= '<' | '<=' | '>' | '>='
; compare_expression ::=
;    shift_expression { compare_op { attribute_instance } shift_expression }
;
; equality_op ::= '==' | '!=' | '===' | '!=='
;               | '==?' | '!=?'                    (SystemVerilog additions)
;
; equality_expression ::=
;    compare_expression { equality_op { attribute_instance } compare_expression }
;
; bitand_expression ::=
;     equality_expression { '&' { attribute_instance } equality_expression }
;
; bitxor_op ::= '^' | '^~' | '~^'
; bitxor_expression ::=
;    bitand_expression { bitxor_op { attribute_instance } bitand_expression }
;
; bitor_expression ::=
;    bitxor_expression { '|' { attribute_instance } bitxor_expression }
;
; logand_expression ::=
;    bitor_expression { '&&' { attribute_instance } bitor_expression }
;
; logor_expression ::=
;    logand_expression { '||' { attribute_instance } logand_expression }
;
; qmark_expression ::=
;    logor_expression { '?' { attribute_instance } expression ':' qmark_expression }
;                                                  ^^ subtle!      ^^ subtle!
; SystemVerilog addition:
;
; impl_op ::= '->' | '<->'   But note these are right associative!
; impl_expression ::=
;    qmark_expression { '->' { attribute_instance } impl_expression }
;
; Note that we deal with assignment operators separately -- see the comments in
; vl-parse-mintypmax-expression.
;
; expression ::= impl_expression

  (defparser vl-parse-unary-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 50)

    ;; unary_expression ::=
    ;;    unary_operator { attribute_instance } primary
    ;;  | primary
    ;;
    ;; SystemVerilog pre-increment operators are:
    ;;    inc_or_dec_expression ::= inc_or_dec_operator { attribute_instance } variable_lvalue      ;; pre increments
    ;;                            | variable_lvalue { attribute_instance } inc_or_dec_operator      ;; post increments
    ;;
    ;; We don't handle post-increments here, but the pre-increments fit perfectly here.

    (seq tokstream

         (op := (if (eq (vl-loadconfig->edition config) :verilog-2005)
                    (vl-parse-op 1 '((:vl-plus   . :vl-unary-plus)   ;;; +
                                     (:vl-minus  . :vl-unary-minus)  ;;; -
                                     (:vl-lognot . :vl-unary-lognot) ;;; !
                                     (:vl-bitnot . :vl-unary-bitnot) ;;; ~
                                     (:vl-bitand . :vl-unary-bitand) ;;; &
                                     (:vl-nand   . :vl-unary-nand)   ;;; ~&
                                     (:vl-bitor  . :vl-unary-bitor)  ;;; |
                                     (:vl-nor    . :vl-unary-nor)    ;;; ~|
                                     (:vl-xor    . :vl-unary-xor)    ;;; ^
                                     (:vl-xnor   . :vl-unary-xnor)   ;;; ~^ or ^~
                                     ))
                  ;; SystemVerilog mode:
                  (vl-parse-op 1 '(;; All the same operators as above...
                                   (:vl-plus   . :vl-unary-plus)   ;;; +
                                   (:vl-minus  . :vl-unary-minus)  ;;; -
                                   (:vl-lognot . :vl-unary-lognot) ;;; !
                                   (:vl-bitnot . :vl-unary-bitnot) ;;; ~
                                   (:vl-bitand . :vl-unary-bitand) ;;; &
                                   (:vl-nand   . :vl-unary-nand)   ;;; ~&
                                   (:vl-bitor  . :vl-unary-bitor)  ;;; |
                                   (:vl-nor    . :vl-unary-nor)    ;;; ~|
                                   (:vl-xor    . :vl-unary-xor)    ;;; ^
                                   (:vl-xnor   . :vl-unary-xnor)   ;;; ~^ or ^~
                                   ;; And also pre increment/decrement
                                   (:vl-plusplus   . :vl-unary-preinc)
                                   (:vl-minusminus . :vl-unary-predec)))))

         (unless op
           (primary :s= (vl-parse-primary))
           (when (eq (vl-loadconfig->edition config) :verilog-2005)
             (return primary))

           ;; SystemVerilog only -- we handle post-increment operators here.
           ;; The rule for post increments is:
           ;;
           ;;     variable_lvalue { attribute_instance } inc_or_dec_operator
           ;;
           ;; so to handle attributes we'll need to backtrack.
           ;;
           ;; Subtle.  This is more permissive than we ought to be, i.e., we
           ;; arguably shouldn't accept input like (a + b)++, but we do
           ;; anyway, under the theory that we'll check for this kind of thing
           ;; later in the increment-elim transform.  If at some point we
           ;; decide this is unacceptable, the easiest fix would be to check
           ;; something like vl-expr-lvaluep here, and only check for post
           ;; increment operators in that case.
           (return-raw
            (b* ((backup (vl-tokstream-save))
                 ((mv err val tokstream)
                  (seq tokstream
                       (atts := (vl-parse-0+-attribute-instances))
                       (post := (vl-parse-op 1 '((:vl-plusplus   . :vl-unary-postinc)
                                                 (:vl-minusminus . :vl-unary-postdec))))
                       (unless post
                         (return nil))

                       (return (make-vl-nonatom :op post
                                                :atts atts
                                                :args (list primary)))))
                 ((when (and (not err) val))
                  (mv nil val tokstream))
                 (tokstream (vl-tokstream-restore backup)))
              (mv nil primary tokstream))))

          (atts :w= (vl-parse-0+-attribute-instances))
          (primary := (vl-parse-primary))

          ;; We had a prefix unary-operator, so we don't need to try to handle
          ;; post-increment/decrement operators here, because no matter what
          ;; the prefix was, it isn't a valid lvalue.  That is, it's malformed
          ;; to try to write stuff like (|a)++ or (++a)++.
          (return (make-vl-nonatom :op   op
                                   :atts atts
                                   :args (list primary)))))


; power_expression ::=
;    unary_expression { '**' { attribute_instance } unary_expression }

  (defparser vl-parse-power-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 60)
    (seq tokstream
          (first :s= (vl-parse-unary-expression))
          (unless (vl-is-token? :vl-power)
            (return (list first)))
          (:= (vl-match))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-power-expression-aux))
          (return (list* first :vl-binary-power atts tail))))

  (defparser vl-parse-power-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 70)
    (seq tokstream
          (mixed := (vl-parse-power-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))




; mult_op ::= '*' | '/' | '%'
; mult_expression ::=
;    power_expression { mult_op { attribute_instance } power_expression }

  (defparser vl-parse-mult-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 80)
    (seq tokstream
          (first :s= (vl-parse-power-expression))
          (op := (vl-parse-op 2 '((:vl-times . :vl-binary-times)
                                  (:vl-div   . :vl-binary-div)
                                  (:vl-rem   . :vl-binary-rem))))
          (unless op
            (return (list first)))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-mult-expression-aux))
          (return (list* first op atts tail))))

  (defparser vl-parse-mult-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 90)
    (seq tokstream
          (mixed := (vl-parse-mult-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; add_op ::= '+' | '-'
; add_expression ::=
;    mult_expression { add_op { attribute_instance } mult_expression }

  (defparser vl-parse-add-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 100)
    (seq tokstream
          (first :s= (vl-parse-mult-expression))
          (op := (vl-parse-op 2 '((:vl-plus  . :vl-binary-plus)
                                  (:vl-minus . :vl-binary-minus))))
          (unless op
            (return (list first)))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-add-expression-aux))
          (return (list* first op atts tail))))

  (defparser vl-parse-add-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 110)
    (seq tokstream
          (mixed := (vl-parse-add-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; shift_op ::= '<<' | '>>' | '<<<' | '>>>'
; shift_expression ::=
;    add_expression { shift_op { attribute_instance } add_expression }

  (defparser vl-parse-shift-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 120)
    (seq tokstream
          (first :s= (vl-parse-add-expression))
          (op := (vl-parse-op 2 '((:vl-shl  . :vl-binary-shl)
                                  (:vl-shr  . :vl-binary-shr)
                                  (:vl-ashl . :vl-binary-ashl)
                                  (:vl-ashr . :vl-binary-ashr))))
          (unless op
            (return (list first)))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-shift-expression-aux))
          (return (list* first op atts tail))))

  (defparser vl-parse-shift-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 130)
    (seq tokstream
          (mixed := (vl-parse-shift-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; compare_op ::= '<' | '<=' | '>' | '>='
; compare_expression ::=
;    shift_expression { compare_op { attribute_instance } shift_expression }

; SystemVerilog adds 'inside' as an operator at this level of precedence as
; well, so we'll add it here.

  (defparser vl-parse-compare-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 140)
    (seq tokstream
          (first :s= (vl-parse-shift-expression))
          (op := (vl-parse-op 2 '((:vl-lt  . :vl-binary-lt)
                                  (:vl-lte . :vl-binary-lte)
                                  (:vl-gt  . :vl-binary-gt)
                                  (:vl-gte . :vl-binary-gte)
                                  (:vl-kwd-inside . :vl-inside)
                                  )))
          (unless op
            (return (list first)))
          (unless (eq op :vl-inside)
            (atts :w= (vl-parse-0+-attribute-instances))
            (tail := (vl-parse-compare-expression-aux))
            (return (list* first op atts tail)))
          ;; Inside operators are special because the second argument is
          ;; a value range list.
          (:= (vl-match-token :vl-lcurly))
          (args := (vl-parse-1+-open-value-ranges))
          (:= (vl-match-token :vl-rcurly))
          (return
           (b* ((tail (make-vl-nonatom :op :vl-valuerangelist
                                       :args args)))
             (list* first op atts (list tail))))))

  (defparser vl-parse-compare-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 150)
    (seq tokstream
          (mixed := (vl-parse-compare-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))

  (defparser vl-parse-open-value-range ()
    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
         (when (vl-is-token? :vl-lbrack)
           ;; We want [ a : b ] here
           (:= (vl-match))
           (a :w= (vl-parse-expression))
           (:= (vl-match-token :vl-colon))
           (b := (vl-parse-expression))
           (:= (vl-match-token :vl-rbrack))
           (return (make-vl-nonatom :op :vl-valuerange
                                    :args (list a b))))
         ;; Otherwise, just an expression
         (return-raw (vl-parse-expression))))


  (defparser vl-parse-1+-open-value-ranges ()
    :measure (two-nats-measure (vl-tokstream-measure) 320)
    (seq tokstream
         (range1 :s= (vl-parse-open-value-range))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-open-value-ranges)))
         (return (cons range1 rest))))


; equality_op ::= '==' | '!=' | '===' | '!=='
; equality_expression ::=
;    compare_expression { equality_op { attribute_instance } compare_expression }

  (defparser vl-parse-equality-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 160)
    (seq tokstream
          (first :s= (vl-parse-compare-expression))
          (op := (vl-parse-op 2 '((:vl-eq      . :vl-binary-eq)
                                  (:vl-neq     . :vl-binary-neq)
                                  (:vl-ceq     . :vl-binary-ceq)
                                  (:vl-cne     . :vl-binary-cne)
                                  (:vl-wildeq  . :vl-binary-wildeq)
                                  (:vl-wildneq . :vl-binary-wildneq))))
          (unless op
            (return (list first)))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-equality-expression-aux))
          (return (list* first op atts tail))))

  (defparser vl-parse-equality-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 170)
    (seq tokstream
          (mixed := (vl-parse-equality-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; bitand_expression ::=
;     equality_expression { '&' { attribute_instance } equality_expression }

  (defparser vl-parse-bitand-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 180)
    (seq tokstream
          (first :s= (vl-parse-equality-expression))
          (unless (vl-is-token? :vl-bitand)
            (return (list first)))
          (:= (vl-match))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitand-expression-aux))
          (return (list* first :vl-binary-bitand atts tail))))

  (defparser vl-parse-bitand-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 190)
    (seq tokstream
          (mixed := (vl-parse-bitand-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; bitxor_op ::= '^' | '^~' | '~^'
; bitxor_expression ::=
;    bitand_expression { bitxor_op { attribute_instance } bitand_expression }

  (defparser vl-parse-bitxor-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 200)
    (seq tokstream
          (first :s= (vl-parse-bitand-expression))
          (op := (vl-parse-op 2 '((:vl-xor . :vl-binary-xor)
                                  (:vl-xnor . :vl-binary-xnor))))
          (unless op
            (return (list first)))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitxor-expression-aux))
          (return (list* first op atts tail))))

  (defparser vl-parse-bitxor-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 210)
    (seq tokstream
          (mixed := (vl-parse-bitxor-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; bitor_expression ::=
;    bitxor_expression { '|' { attribute_instance } bitxor_expression }

  (defparser vl-parse-bitor-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 220)
    (seq tokstream
          (first :s= (vl-parse-bitxor-expression))
          (unless (vl-is-token? :vl-bitor)
            (return (list first)))
          (:= (vl-match))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitor-expression-aux))
          (return (list* first :vl-binary-bitor atts tail))))

  (defparser vl-parse-bitor-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 230)
    (seq tokstream
          (mixed := (vl-parse-bitor-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; logand_expression ::=
;    bitor_expression { '&&' { attribute_instance } bitor_expression }

  (defparser vl-parse-logand-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 240)
    (seq tokstream
          (first :s= (vl-parse-bitor-expression))
          (unless (vl-is-token? :vl-logand)
            (return (list first)))
          (:= (vl-match))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-logand-expression-aux))
          (return (list* first :vl-binary-logand atts tail))))

  (defparser vl-parse-logand-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 250)
    (seq tokstream
          (mixed := (vl-parse-logand-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; logor_expression ::=
;    logand_expression { '||' { attribute_instance } logand_expression }

  (defparser vl-parse-logor-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 260)
    (seq tokstream
          (first :s= (vl-parse-logand-expression))
          (unless (vl-is-token? :vl-logor)
            (return (list first)))
          (:= (vl-match))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-logor-expression-aux))
          (return (list* first :vl-binary-logor atts tail))))

  (defparser vl-parse-logor-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 270)
    (seq tokstream
          (mixed := (vl-parse-logor-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))


; qmark_expression ::=
;    logor_expression { '?' { attribute_instance } expression ':' qmark_expression }
;                                                  ^^ subtle      ^^ subtle
;
; Note that the conditional operator associates to the right, so for
; example
;    1 ? 2 : 3 ? 4 : 5
;
; Should be interpreted as:  1 ? 2 : (3 ? 4 : 5)   =  2
; Rather than as:            (1 ? 2 : 3) ? 4 : 5   =  4

  (defparser vl-parse-qmark-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 280)
    (seq tokstream
          (first :s= (vl-parse-logor-expression))
          (unless (vl-is-token? :vl-qmark)
            (return first))
          (:= (vl-match))
          (atts :w= (vl-parse-0+-attribute-instances))
          ;; Subtle!.  The middle expression needs to not be just a
          ;; qmark_expression, because that wouldn't match lower-precedence
          ;; things, e.g., for 1 ? 2 -> 3 : 4 to work, we need the middle
          ;; expression to be an arbitrary expression.
          (second :s= (vl-parse-expression))
          (:= (vl-match-token :vl-colon))
          ;; Subtle!  The third expression needs to ONLY be a qmark expression.
          ;; We don't want to match, e.g., the 3->4 part of 1 ? 2 : 3->4,
          ;; because the -> has lower precedence than the ?:, so we need to
          ;; treat that as (1?2:3) -> 4 instead.
          (third := (vl-parse-qmark-expression))
          (return (make-vl-nonatom :op :vl-qmark
                                   :atts atts
                                   :args (list first second third)))))

; SystemVerilog addition:
;
; impl_op ::= '->' | '<->'
; impl_expression ::=
;    qmark_expression { '->' { attribute_instance } impl_expression }
;
; Note: unlike other binary operators, these associate to the right, e.g., a ->
; b -> c should be interpreted as a -> (b -> c) instead of (a -> b) -> c.
; Hence we don't need to do any mixed-binop-list nonsense.

  (defparser vl-parse-impl-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 290)
    (seq tokstream
          (first :s= (vl-parse-qmark-expression))
          (when (eq (vl-loadconfig->edition config) :verilog-2005)
            ;; Implies/equiv aren't supported in Verilog-2005.
            (return first))
          (op := (vl-parse-op 2 '((:vl-arrow . :vl-implies)
                                  (:vl-equiv . :vl-equiv))))
          (unless op
            (return first))
          (atts :w= (vl-parse-0+-attribute-instances))
          (second :s= (vl-parse-impl-expression))
          (return (make-vl-nonatom :op op
                                   :args (list first second)
                                   :atts atts))))





  (defparser vl-parse-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 300)
    (seq tokstream
          (unless (and (vl-is-token? :vl-kwd-tagged)
                       (not (eq (vl-loadconfig->edition config) :verilog-2005)))
            (expr :s= (vl-parse-impl-expression))
            (return expr))

          ;; tagged_union_expression ::= tagged id [expression]
          (:= (vl-match))
          (id := (vl-match-token :vl-idtoken))
          (return-raw
           (b* ((tagexpr (make-vl-atom :guts (make-vl-tagname :name (vl-idtoken->name id))))
                (backup  (vl-tokstream-save))
                ((mv err expr tokstream)
                 (seq tokstream
                       (expr :s= (vl-parse-expression))
                       (return expr)))
                ((when err)
                 ;; No subsequent expression is fine.
                 (b* ((tokstream (vl-tokstream-restore backup)))
                   (mv nil (make-vl-nonatom :op :vl-tagged :args (list tagexpr))
                       tokstream)))

                ;; Well, what a nightmare.  This is completely ambiguous, and
                ;; VCS/NCVerilog don't implement it yet, so there's no way to
                ;; test what commercial simulators do.  Well-played, IEEE.  The
                ;; following is totally gross, but maybe sort of reasonable?
                ;; Maybe we can rework it, if this ever gets straightened out.
                ((unless (or (vl-fast-atom-p expr)
                             (hons-assoc-equal "VL_EXPLICIT_PARENS"
                                               (vl-nonatom->atts expr))))
                 (vl-parse-error
                  "Cowardly refusing to support tagged union expression such as
                   'tagged foo 1 + 2' due to unclear precedence.  Workaround:
                   add explicit parens, e.g., write 'tagged foo (1 + 2)'
                   instead."))

                (ans (make-vl-nonatom :op :vl-tagged
                                      :args (list tagexpr expr))))
             (mv nil ans tokstream))))))


(defun vl-val-when-error-claim-fn (name args)
  `'(,name (implies (mv-nth 0 (,name . ,args))
                    (equal (mv-nth 1 (,name . ,args))
                           nil))))

(defmacro vl-val-when-error-claim (name &key args)
  (vl-val-when-error-claim-fn name args))

(with-output
  :gag-mode :goals
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil))
 (encapsulate
  ()
  (local (in-theory (disable vl-is-token?-fn-when-atom-of-tokens
                           acl2::append-under-iff
                           (:t len)
                           (:t vl-is-token?)
                           (force)
                           acl2::len-when-atom)))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-val-when-error
      ,(vl-val-when-error-claim vl-parse-attr-spec)
      ,(vl-val-when-error-claim vl-parse-attribute-instance-aux)
      ,(vl-val-when-error-claim vl-parse-attribute-instance)
      ,(vl-val-when-error-claim vl-parse-0+-attribute-instances-aux)
      ,(vl-val-when-error-claim vl-parse-0+-attribute-instances)
      ,(vl-val-when-error-claim vl-parse-1+-expressions-separated-by-commas)
      ,(vl-val-when-error-claim vl-parse-system-function-call)
      ,(vl-val-when-error-claim vl-parse-mintypmax-expression)
      ,(vl-val-when-error-claim vl-parse-range-expression)
      ,(vl-val-when-error-claim vl-parse-concatenation)
      ,(vl-val-when-error-claim vl-parse-stream-expression)
      ,(vl-val-when-error-claim vl-parse-stream-concatenation)
      ,(vl-val-when-error-claim vl-parse-1+-stream-expressions-separated-by-commas)
      ,(vl-val-when-error-claim vl-parse-simple-type)
      ,(vl-val-when-error-claim vl-parse-slice-size)
      ,(vl-val-when-error-claim vl-parse-any-sort-of-concatenation)
      ,(vl-val-when-error-claim vl-parse-hierarchical-identifier :args (recursivep))
      ,(vl-val-when-error-claim vl-parse-function-call)
      ,(vl-val-when-error-claim vl-parse-0+-bracketed-expressions)
      ,(vl-val-when-error-claim vl-parse-indexed-id-2005 :args (scopes recursivep))
      ,(vl-val-when-error-claim vl-parse-indexed-id-2012)
      ,(vl-val-when-error-claim vl-parse-indexed-id)
      ,(vl-val-when-error-claim vl-parse-assignment-pattern)
      ,(vl-val-when-error-claim vl-parse-1+-keyval-expression-pairs)
      ,(vl-val-when-error-claim vl-parse-primary-main)
      ,(vl-val-when-error-claim vl-parse-primary-cast)
      ,(vl-val-when-error-claim vl-parse-nonprimary-cast)
      ,(vl-val-when-error-claim vl-parse-primary)
      ,(vl-val-when-error-claim vl-parse-unary-expression)
      ,(vl-val-when-error-claim vl-parse-power-expression-aux)
      ,(vl-val-when-error-claim vl-parse-power-expression)
      ,(vl-val-when-error-claim vl-parse-mult-expression-aux)
      ,(vl-val-when-error-claim vl-parse-mult-expression)
      ,(vl-val-when-error-claim vl-parse-add-expression-aux)
      ,(vl-val-when-error-claim vl-parse-add-expression)
      ,(vl-val-when-error-claim vl-parse-shift-expression-aux)
      ,(vl-val-when-error-claim vl-parse-shift-expression)
      ,(vl-val-when-error-claim vl-parse-compare-expression-aux)
      ,(vl-val-when-error-claim vl-parse-compare-expression)
      ,(vl-val-when-error-claim vl-parse-equality-expression-aux)
      ,(vl-val-when-error-claim vl-parse-equality-expression)
      ,(vl-val-when-error-claim vl-parse-bitand-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitand-expression)
      ,(vl-val-when-error-claim vl-parse-bitxor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitxor-expression)
      ,(vl-val-when-error-claim vl-parse-bitor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitor-expression)
      ,(vl-val-when-error-claim vl-parse-logand-expression-aux)
      ,(vl-val-when-error-claim vl-parse-logand-expression)
      ,(vl-val-when-error-claim vl-parse-logor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-logor-expression)
      ,(vl-val-when-error-claim vl-parse-qmark-expression)
      ,(vl-val-when-error-claim vl-parse-impl-expression)
      ,(vl-val-when-error-claim vl-parse-open-value-range)
      ,(vl-val-when-error-claim vl-parse-1+-open-value-ranges)
      ,(vl-val-when-error-claim vl-parse-expression)
      :hints((and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))


(defun vl-warning-claim-fn (name args)
  `'(,name (iff (vl-warning-p (mv-nth 0 (,name . ,args)))
                (mv-nth 0 (,name . ,args)))))

(defmacro vl-warning-claim (name &key args)
  (vl-warning-claim-fn name args))

(with-output
  :off prove :gag-mode :goals
  (encapsulate
    ()
    (local (in-theory (disable (force) iff
                               vl-is-token?-fn-when-atom-of-tokens
                               acl2::append-under-iff
                               (:t len)
                               (:t vl-is-token?)
                               ;; acl2::mv-nth-cons-meta
                               (force)
                               acl2::len-when-atom)))
    (make-event
     `(defthm-parse-expressions-flag vl-parse-expression-warning
        ,(vl-warning-claim vl-parse-attr-spec)
        ,(vl-warning-claim vl-parse-attribute-instance-aux)
        ,(vl-warning-claim vl-parse-attribute-instance)
        ,(vl-warning-claim vl-parse-0+-attribute-instances-aux)
        ,(vl-warning-claim vl-parse-0+-attribute-instances)
        ,(vl-warning-claim vl-parse-1+-expressions-separated-by-commas)
        ,(vl-warning-claim vl-parse-system-function-call)
        ,(vl-warning-claim vl-parse-mintypmax-expression)
        ,(vl-warning-claim vl-parse-range-expression)
        ,(vl-warning-claim vl-parse-concatenation)
        ,(vl-warning-claim vl-parse-stream-expression)
        ,(vl-warning-claim vl-parse-stream-concatenation)
        ,(vl-warning-claim vl-parse-1+-stream-expressions-separated-by-commas)
        ,(vl-warning-claim vl-parse-simple-type)
        ,(vl-warning-claim vl-parse-slice-size)
        ,(vl-warning-claim vl-parse-any-sort-of-concatenation)
        ,(vl-warning-claim vl-parse-hierarchical-identifier :args (recursivep))
        ,(vl-warning-claim vl-parse-function-call)
        ,(vl-warning-claim vl-parse-0+-bracketed-expressions)
        ,(vl-warning-claim vl-parse-indexed-id-2005 :args (scopes recursivep))
        ,(vl-warning-claim vl-parse-indexed-id-2012)
        ,(vl-warning-claim vl-parse-indexed-id)
        ,(vl-warning-claim vl-parse-primary-main)
        ,(vl-warning-claim vl-parse-primary-cast)
        ,(vl-warning-claim vl-parse-nonprimary-cast)
        ,(vl-warning-claim vl-parse-primary)
        ,(vl-warning-claim vl-parse-unary-expression)
        ,(vl-warning-claim vl-parse-power-expression-aux)
        ,(vl-warning-claim vl-parse-power-expression)
        ,(vl-warning-claim vl-parse-mult-expression-aux)
        ,(vl-warning-claim vl-parse-mult-expression)
        ,(vl-warning-claim vl-parse-add-expression-aux)
        ,(vl-warning-claim vl-parse-add-expression)
        ,(vl-warning-claim vl-parse-shift-expression-aux)
        ,(vl-warning-claim vl-parse-shift-expression)
        ,(vl-warning-claim vl-parse-compare-expression-aux)
        ,(vl-warning-claim vl-parse-compare-expression)
        ,(vl-warning-claim vl-parse-equality-expression-aux)
        ,(vl-warning-claim vl-parse-equality-expression)
        ,(vl-warning-claim vl-parse-bitand-expression-aux)
        ,(vl-warning-claim vl-parse-bitand-expression)
        ,(vl-warning-claim vl-parse-bitxor-expression-aux)
        ,(vl-warning-claim vl-parse-bitxor-expression)
        ,(vl-warning-claim vl-parse-bitor-expression-aux)
        ,(vl-warning-claim vl-parse-bitor-expression)
        ,(vl-warning-claim vl-parse-logand-expression-aux)
        ,(vl-warning-claim vl-parse-logand-expression)
        ,(vl-warning-claim vl-parse-logor-expression-aux)
        ,(vl-warning-claim vl-parse-logor-expression)
        ,(vl-warning-claim vl-parse-qmark-expression)
        ,(vl-warning-claim vl-parse-impl-expression)
        ,(vl-warning-claim vl-parse-open-value-range)
        ,(vl-warning-claim vl-parse-1+-open-value-ranges)
        ,(vl-warning-claim vl-parse-assignment-pattern)
        ,(vl-warning-claim vl-parse-1+-keyval-expression-pairs)
        ,(vl-warning-claim vl-parse-expression)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))



;; (defun vl-tokenlist-claim-fn (name args)
;;   `'(,name (vl-tokenlist-p (mv-nth 2 (,name . ,args)))))

;; (defmacro vl-tokenlist-claim (name &key args)
;;   (vl-tokenlist-claim-fn name args))

;; (with-output
;;   :off prove
;;   :gag-mode :goals
;;  (make-event
;;   `(defthm-parse-expressions-flag vl-parse-expression-tokenlist
;;      ,(vl-tokenlist-claim vl-parse-attr-spec)
;;      ,(vl-tokenlist-claim vl-parse-attribute-instance-aux)
;;      ,(vl-tokenlist-claim vl-parse-attribute-instance)
;;      ,(vl-tokenlist-claim vl-parse-0+-attribute-instances-aux)
;;      ,(vl-tokenlist-claim vl-parse-0+-attribute-instances)
;;      ,(vl-tokenlist-claim vl-parse-1+-expressions-separated-by-commas)
;;      ,(vl-tokenlist-claim vl-parse-system-function-call)
;;      ,(vl-tokenlist-claim vl-parse-mintypmax-expression)
;;      ,(vl-tokenlist-claim vl-parse-range-expression)
;;      ,(vl-tokenlist-claim vl-parse-concatenation)
;;      ,(vl-tokenlist-claim vl-parse-stream-expression)
;;      ,(vl-tokenlist-claim vl-parse-stream-concatenation)
;;      ,(vl-tokenlist-claim vl-parse-1+-stream-expressions-separated-by-commas)
;;      ,(vl-tokenlist-claim vl-parse-simple-type)
;;      ,(vl-tokenlist-claim vl-parse-slice-size)
;;      ,(vl-tokenlist-claim vl-parse-any-sort-of-concatenation)
;;      ,(vl-tokenlist-claim vl-parse-hierarchical-identifier :args (recursivep))
;;      ,(vl-tokenlist-claim vl-parse-function-call)
;;      ,(vl-tokenlist-claim vl-parse-0+-bracketed-expressions)
;;      ,(vl-tokenlist-claim vl-parse-indexed-id)
;;      ,(vl-tokenlist-claim vl-parse-primary-main)
;;      ,(vl-tokenlist-claim vl-parse-primary-cast)
;;      ,(vl-tokenlist-claim vl-parse-nonprimary-cast)
;;      ,(vl-tokenlist-claim vl-parse-primary)
;;      ,(vl-tokenlist-claim vl-parse-unary-expression)
;;      ,(vl-tokenlist-claim vl-parse-power-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-power-expression)
;;      ,(vl-tokenlist-claim vl-parse-mult-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-mult-expression)
;;      ,(vl-tokenlist-claim vl-parse-add-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-add-expression)
;;      ,(vl-tokenlist-claim vl-parse-shift-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-shift-expression)
;;      ,(vl-tokenlist-claim vl-parse-compare-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-compare-expression)
;;      ,(vl-tokenlist-claim vl-parse-equality-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-equality-expression)
;;      ,(vl-tokenlist-claim vl-parse-bitand-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-bitand-expression)
;;      ,(vl-tokenlist-claim vl-parse-bitxor-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-bitxor-expression)
;;      ,(vl-tokenlist-claim vl-parse-bitor-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-bitor-expression)
;;      ,(vl-tokenlist-claim vl-parse-logand-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-logand-expression)
;;      ,(vl-tokenlist-claim vl-parse-logor-expression-aux)
;;      ,(vl-tokenlist-claim vl-parse-logor-expression)
;;      ,(vl-tokenlist-claim vl-parse-qmark-expression)
;;      ,(vl-tokenlist-claim vl-parse-impl-expression)
;;      ,(vl-tokenlist-claim vl-parse-expression)
;;      :hints((and acl2::stable-under-simplificationp
;;                  (flag::expand-calls-computed-hint
;;                   acl2::clause
;;                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))))))

;; (defun vl-parsestate-claim-fn (name args)
;;   `'(,name (vl-parsestate-p (mv-nth 3 (,name . ,args)))))

;; (defmacro vl-parsestate-claim (name &key args)
;;   (vl-parsestate-claim-fn name args))

;; (with-output
;;   :off prove
;;   :gag-mode :goals
;;   (make-event
;;    `(defthm-parse-expressions-flag vl-parse-expression-parsestate
;;       ,(vl-parsestate-claim vl-parse-attr-spec)
;;       ,(vl-parsestate-claim vl-parse-attribute-instance-aux)
;;       ,(vl-parsestate-claim vl-parse-attribute-instance)
;;       ,(vl-parsestate-claim vl-parse-0+-attribute-instances-aux)
;;       ,(vl-parsestate-claim vl-parse-0+-attribute-instances)
;;       ,(vl-parsestate-claim vl-parse-1+-expressions-separated-by-commas)
;;       ,(vl-parsestate-claim vl-parse-system-function-call)
;;       ,(vl-parsestate-claim vl-parse-mintypmax-expression)
;;       ,(vl-parsestate-claim vl-parse-range-expression)
;;       ,(vl-parsestate-claim vl-parse-concatenation)
;;       ,(vl-parsestate-claim vl-parse-stream-expression)
;;       ,(vl-parsestate-claim vl-parse-stream-concatenation)
;;       ,(vl-parsestate-claim vl-parse-1+-stream-expressions-separated-by-commas)
;;       ,(vl-parsestate-claim vl-parse-simple-type)
;;       ,(vl-parsestate-claim vl-parse-slice-size)
;;       ,(vl-parsestate-claim vl-parse-any-sort-of-concatenation)
;;       ,(vl-parsestate-claim vl-parse-hierarchical-identifier :args (recursivep))
;;       ,(vl-parsestate-claim vl-parse-function-call)
;;       ,(vl-parsestate-claim vl-parse-0+-bracketed-expressions)
;;       ,(vl-parsestate-claim vl-parse-indexed-id)
;;       ,(vl-parsestate-claim vl-parse-primary-main)
;;       ,(vl-parsestate-claim vl-parse-primary-cast)
;;       ,(vl-parsestate-claim vl-parse-nonprimary-cast)
;;       ,(vl-parsestate-claim vl-parse-primary)
;;       ,(vl-parsestate-claim vl-parse-unary-expression)
;;       ,(vl-parsestate-claim vl-parse-power-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-power-expression)
;;       ,(vl-parsestate-claim vl-parse-mult-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-mult-expression)
;;       ,(vl-parsestate-claim vl-parse-add-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-add-expression)
;;       ,(vl-parsestate-claim vl-parse-shift-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-shift-expression)
;;       ,(vl-parsestate-claim vl-parse-compare-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-compare-expression)
;;       ,(vl-parsestate-claim vl-parse-equality-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-equality-expression)
;;       ,(vl-parsestate-claim vl-parse-bitand-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-bitand-expression)
;;       ,(vl-parsestate-claim vl-parse-bitxor-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-bitxor-expression)
;;       ,(vl-parsestate-claim vl-parse-bitor-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-bitor-expression)
;;       ,(vl-parsestate-claim vl-parse-logand-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-logand-expression)
;;       ,(vl-parsestate-claim vl-parse-logor-expression-aux)
;;       ,(vl-parsestate-claim vl-parse-logor-expression)
;;       ,(vl-parsestate-claim vl-parse-qmark-expression)
;;       ,(vl-parsestate-claim vl-parse-impl-expression)
;;       ,(vl-parsestate-claim vl-parse-expression)
;;       :hints(("Goal" :in-theory (disable (force)))
;;              (and acl2::stable-under-simplificationp
;;                   (flag::expand-calls-computed-hint
;;                    acl2::clause
;;                    ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))))))

(defun vl-progress-claim-fn (name strongp args)
  `'(,name (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,args)))
                    (vl-tokstream-measure))
                ,@(if strongp
                      `((implies (not (mv-nth 0 (,name . ,args)))
                                 (< (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,args)))
                                    (vl-tokstream-measure))))
                    nil))
           :rule-classes ((:rewrite) (:linear))))

(defmacro vl-progress-claim (name &key
                                  (strongp 't)
                                  args)
  (vl-progress-claim-fn name strongp args))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (disable (force) iff
                             vl-is-token?-fn-when-atom-of-tokens
                             acl2::append-under-iff
                             (:t len)
                             (:t vl-is-token?)
                             ;; acl2::mv-nth-cons-meta
                             (force)
                             acl2::len-when-atom
                             acl2::cancel_plus-lessp-correct
                             acl2::leq-position-equal-len
                             str::count-leading-charset-len
                             (:t vl-loadconfig->edition)
                             booleanp-of-vl-parsestate-is-user-defined-type-p
                             (:t vl-parsestate-is-user-defined-type-p)
                             (:t vl-expr-kind)
                             (:t vl-lookahead-is-token?)
                             (:t vl-lookahead-is-token?-fn-when-atom-of-tokens))))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-progress
      ,(vl-progress-claim vl-parse-attr-spec)
      ,(vl-progress-claim vl-parse-attribute-instance-aux)
      ,(vl-progress-claim vl-parse-attribute-instance)
      ,(vl-progress-claim vl-parse-0+-attribute-instances-aux :strongp nil)
      ,(vl-progress-claim vl-parse-0+-attribute-instances :strongp nil)
      ,(vl-progress-claim vl-parse-1+-expressions-separated-by-commas)
      ,(vl-progress-claim vl-parse-system-function-call)
      ,(vl-progress-claim vl-parse-mintypmax-expression)
      ,(vl-progress-claim vl-parse-range-expression)
      ,(vl-progress-claim vl-parse-concatenation)
      ,(vl-progress-claim vl-parse-stream-expression)
      ,(vl-progress-claim vl-parse-stream-concatenation)
      ,(vl-progress-claim vl-parse-1+-stream-expressions-separated-by-commas)
      ,(vl-progress-claim vl-parse-simple-type)
      ,(vl-progress-claim vl-parse-slice-size)
      ,(vl-progress-claim vl-parse-any-sort-of-concatenation)
      ,(vl-progress-claim vl-parse-hierarchical-identifier :args (recursivep))
      ,(vl-progress-claim vl-parse-function-call)
      ,(vl-progress-claim vl-parse-0+-bracketed-expressions :strongp nil)
      ,(vl-progress-claim vl-parse-indexed-id-2005 :args (scopes recursivep))
      ,(vl-progress-claim vl-parse-indexed-id-2012)
      ,(vl-progress-claim vl-parse-indexed-id)
      ,(vl-progress-claim vl-parse-primary-main)
      ,(vl-progress-claim vl-parse-primary-cast)
      ,(vl-progress-claim vl-parse-nonprimary-cast)
      ,(vl-progress-claim vl-parse-primary)
      ,(vl-progress-claim vl-parse-unary-expression)
      ,(vl-progress-claim vl-parse-power-expression-aux)
      ,(vl-progress-claim vl-parse-power-expression)
      ,(vl-progress-claim vl-parse-mult-expression-aux)
      ,(vl-progress-claim vl-parse-mult-expression)
      ,(vl-progress-claim vl-parse-add-expression-aux)
      ,(vl-progress-claim vl-parse-add-expression)
      ,(vl-progress-claim vl-parse-shift-expression-aux)
      ,(vl-progress-claim vl-parse-shift-expression)
      ,(vl-progress-claim vl-parse-compare-expression-aux)
      ,(vl-progress-claim vl-parse-compare-expression)
      ,(vl-progress-claim vl-parse-equality-expression-aux)
      ,(vl-progress-claim vl-parse-equality-expression)
      ,(vl-progress-claim vl-parse-bitand-expression-aux)
      ,(vl-progress-claim vl-parse-bitand-expression)
      ,(vl-progress-claim vl-parse-bitxor-expression-aux)
      ,(vl-progress-claim vl-parse-bitxor-expression)
      ,(vl-progress-claim vl-parse-bitor-expression-aux)
      ,(vl-progress-claim vl-parse-bitor-expression)
      ,(vl-progress-claim vl-parse-logand-expression-aux)
      ,(vl-progress-claim vl-parse-logand-expression)
      ,(vl-progress-claim vl-parse-logor-expression-aux)
      ,(vl-progress-claim vl-parse-logor-expression)
      ,(vl-progress-claim vl-parse-qmark-expression)
      ,(vl-progress-claim vl-parse-impl-expression)
      ,(vl-progress-claim vl-parse-assignment-pattern)
      ,(vl-progress-claim vl-parse-1+-keyval-expression-pairs)
      ,(vl-progress-claim vl-parse-open-value-range)
      ,(vl-progress-claim vl-parse-1+-open-value-ranges)
      ,(vl-progress-claim vl-parse-expression)
      :hints((and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))

(defun vl-eof-claim-fn (name args type)
  `'(,name (implies (atom (vl-tokstream->tokens))
                    ,(cond ((eq type :error)
                            `(mv-nth 0 (,name . ,args)))
                           ((eq type nil)
                            `(equal (mv-nth 1 (,name . ,args))
                                    nil))
                           (t
                            (er hard? 'vl-eof-claim-fn
                                "Bad type: ~x0." type))))))

(defmacro vl-eof-claim (name type &key args)
  (vl-eof-claim-fn name args type))

(with-output
  :off prove
  :gag-mode :goals
  (encapsulate
    ()
    (local (in-theory (disable (force))))
    (local (in-theory (enable tokens-nonempty-when-vl-maybe-parse-base-primary)))
    (make-event
     `(defthm-parse-expressions-flag vl-parse-expression-eof
        ,(vl-eof-claim vl-parse-attr-spec :error)
        ,(vl-eof-claim vl-parse-attribute-instance-aux :error)
        ,(vl-eof-claim vl-parse-attribute-instance :error)
        ,(vl-eof-claim vl-parse-0+-attribute-instances-aux nil)
        ,(vl-eof-claim vl-parse-0+-attribute-instances nil)
        ,(vl-eof-claim vl-parse-1+-expressions-separated-by-commas :error)
        ,(vl-eof-claim vl-parse-system-function-call :error)
        ,(vl-eof-claim vl-parse-mintypmax-expression :error)
        ,(vl-eof-claim vl-parse-range-expression :error)
        ,(vl-eof-claim vl-parse-concatenation :error)
        ,(vl-eof-claim vl-parse-stream-expression :error)
        ,(vl-eof-claim vl-parse-stream-concatenation :error)
        ,(vl-eof-claim vl-parse-1+-stream-expressions-separated-by-commas :error)
        ,(vl-eof-claim vl-parse-simple-type :error)
        ,(vl-eof-claim vl-parse-slice-size :error)
        ,(vl-eof-claim vl-parse-any-sort-of-concatenation :error)
        ,(vl-eof-claim vl-parse-hierarchical-identifier :error :args (recursivep))
        ,(vl-eof-claim vl-parse-function-call :error)
        ,(vl-eof-claim vl-parse-0+-bracketed-expressions nil)
        ,(vl-eof-claim vl-parse-indexed-id-2005 :error :args (scopes recursivep))
        ,(vl-eof-claim vl-parse-indexed-id-2012 :error)
        ,(vl-eof-claim vl-parse-indexed-id :error)
        ,(vl-eof-claim vl-parse-primary-main :error)
        ,(vl-eof-claim vl-parse-primary-cast :error)
        ,(vl-eof-claim vl-parse-nonprimary-cast :error)
        ,(vl-eof-claim vl-parse-primary :error)
        ,(vl-eof-claim vl-parse-unary-expression :error)
        ,(vl-eof-claim vl-parse-power-expression-aux :error)
        ,(vl-eof-claim vl-parse-power-expression :error)
        ,(vl-eof-claim vl-parse-mult-expression-aux :error)
        ,(vl-eof-claim vl-parse-mult-expression :error)
        ,(vl-eof-claim vl-parse-add-expression-aux :error)
        ,(vl-eof-claim vl-parse-add-expression :error)
        ,(vl-eof-claim vl-parse-shift-expression-aux :error)
        ,(vl-eof-claim vl-parse-shift-expression :error)
        ,(vl-eof-claim vl-parse-compare-expression-aux :error)
        ,(vl-eof-claim vl-parse-compare-expression :error)
        ,(vl-eof-claim vl-parse-equality-expression-aux :error)
        ,(vl-eof-claim vl-parse-equality-expression :error)
        ,(vl-eof-claim vl-parse-bitand-expression-aux :error)
        ,(vl-eof-claim vl-parse-bitand-expression :error)
        ,(vl-eof-claim vl-parse-bitxor-expression-aux :error)
        ,(vl-eof-claim vl-parse-bitxor-expression :error)
        ,(vl-eof-claim vl-parse-bitor-expression-aux :error)
        ,(vl-eof-claim vl-parse-bitor-expression :error)
        ,(vl-eof-claim vl-parse-logand-expression-aux :error)
        ,(vl-eof-claim vl-parse-logand-expression :error)
        ,(vl-eof-claim vl-parse-logor-expression-aux :error)
        ,(vl-eof-claim vl-parse-logor-expression :error)
        ,(vl-eof-claim vl-parse-qmark-expression :error)
        ,(vl-eof-claim vl-parse-impl-expression :error)
        ,(vl-eof-claim vl-parse-assignment-pattern :error)
        ,(vl-eof-claim vl-parse-1+-keyval-expression-pairs :error)
        ,(vl-eof-claim vl-parse-open-value-range :error)
        ,(vl-eof-claim vl-parse-1+-open-value-ranges :error)
        ,(vl-eof-claim vl-parse-expression :error)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))



(defun vl-expression-claim-fn (name args type)
  `'(,name (implies (force (not (mv-nth 0 (,name . ,args))))
                    ,(cond ((eq type :expr)
                            `(vl-expr-p (mv-nth 1 (,name . ,args))))
                           ((eq type :exprlist)
                            `(vl-exprlist-p (mv-nth 1 (,name . ,args))))
                           ((eq type :atts)
                            `(vl-atts-p (mv-nth 1 (,name . ,args))))
                           ((eq type :erange)
                            `(vl-erange-p (mv-nth 1 (,name . ,args))))
                           ((eq type :mixed)
                            `(vl-mixed-binop-list-p (mv-nth 1 (,name . ,args))))
                           (t
                            (er hard? 'vl-expression-claim-fn
                                "Bad type: ~x0." type))))))

(defmacro vl-expression-claim (name type &key args)
  (vl-expression-claim-fn name args type))

(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ;vl-atom-p-by-tag-when-vl-expr-p
                           )))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (disable ; (force)
                             vl-is-token?-fn-when-atom-of-tokens
                             (:t vl-is-token?)
                             acl2::len-when-atom)))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-value
      ,(vl-expression-claim vl-parse-attr-spec :atts)
      ,(vl-expression-claim vl-parse-attribute-instance-aux :atts)
      ,(vl-expression-claim vl-parse-attribute-instance :atts)
      ,(vl-expression-claim vl-parse-0+-attribute-instances-aux :atts)
      ,(vl-expression-claim vl-parse-0+-attribute-instances :atts)
      ,(vl-expression-claim vl-parse-1+-expressions-separated-by-commas :exprlist)
      ,(vl-expression-claim vl-parse-system-function-call :expr)
      ,(vl-expression-claim vl-parse-mintypmax-expression :expr)
      ,(vl-expression-claim vl-parse-range-expression :erange)
      ,(vl-expression-claim vl-parse-concatenation :expr)
      ,(vl-expression-claim vl-parse-stream-expression :expr)
      ,(vl-expression-claim vl-parse-stream-concatenation :exprlist)
      ,(vl-expression-claim vl-parse-1+-stream-expressions-separated-by-commas :exprlist)
      ,(vl-expression-claim vl-parse-simple-type :expr)
      ,(vl-expression-claim vl-parse-slice-size :expr)
      ,(vl-expression-claim vl-parse-any-sort-of-concatenation :expr)
      ,(vl-expression-claim vl-parse-hierarchical-identifier :expr :args (recursivep))
      ,(vl-expression-claim vl-parse-function-call :expr)
      ,(vl-expression-claim vl-parse-0+-bracketed-expressions :exprlist)
      ,(vl-expression-claim vl-parse-indexed-id-2005 :expr :args (scopes recursivep))
      ,(vl-expression-claim vl-parse-indexed-id-2012 :expr)
      ,(vl-expression-claim vl-parse-indexed-id :expr)
      ,(vl-expression-claim vl-parse-primary-main :expr)
      ,(vl-expression-claim vl-parse-primary-cast :expr)
      ,(vl-expression-claim vl-parse-nonprimary-cast :expr)
      ,(vl-expression-claim vl-parse-primary :expr)
      ,(vl-expression-claim vl-parse-unary-expression :expr)
      ,(vl-expression-claim vl-parse-power-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-power-expression :expr)
      ,(vl-expression-claim vl-parse-mult-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-mult-expression :expr)
      ,(vl-expression-claim vl-parse-add-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-add-expression :expr)
      ,(vl-expression-claim vl-parse-shift-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-shift-expression :expr)
      ,(vl-expression-claim vl-parse-compare-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-compare-expression :expr)
      ,(vl-expression-claim vl-parse-equality-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-equality-expression :expr)
      ,(vl-expression-claim vl-parse-bitand-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-bitand-expression :expr)
      ,(vl-expression-claim vl-parse-bitxor-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-bitxor-expression :expr)
      ,(vl-expression-claim vl-parse-bitor-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-bitor-expression :expr)
      ,(vl-expression-claim vl-parse-logand-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-logand-expression :expr)
      ,(vl-expression-claim vl-parse-logor-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-logor-expression :expr)
      ,(vl-expression-claim vl-parse-qmark-expression :expr)
      ,(vl-expression-claim vl-parse-impl-expression :expr)
      ,(vl-expression-claim vl-parse-assignment-pattern :expr)
      ,(vl-expression-claim vl-parse-1+-keyval-expression-pairs :exprlist)
      ,(vl-expression-claim vl-parse-open-value-range :expr)
      ,(vl-expression-claim vl-parse-1+-open-value-ranges :exprlist)
      ,(vl-expression-claim vl-parse-expression :expr)
      :hints(("Goal"
              :do-not '(generalize fertilize))
             (and stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))
             )))))

(local (defthm true-listp-when-alistp
         (implies (alistp x)
                  (true-listp x))))

(local (in-theory (enable vl-arity-ok-p)))

;; (local (defthm l1
;;          (implies
;;           (VL-LOOKAHEAD-IS-TOKEN? :VL-SCOPE (CDR (VL-TOKSTREAM->TOKENS :TOKSTREAM (LIST TOKSTREAM1 TOKSTREAM3))))
;;           (CONSP
;;            (VL-TOKSTREAM->TOKENS
;;             :TOKSTREAM (MV-NTH 2
;;                                (VL-MATCH :TOKSTREAM (LIST TOKSTREAM1 TOKSTREAM3))))))
;;          :hints(("Goal" :in-theory (enable vl-lookahead-is-token?
;;                                            vl-match)))))

(with-output
  :off (prove event) :gag-mode :goals
 (verify-guards vl-parse-expression-fn
   ;; :guard-debug t
   ))

(defparser-top vl-parse-expression :resulttype vl-expr-p)





;; (defparser vl-parse-ps-class-identifier ()
;;   :short "Match @('ps_class_identifier'), return an expression."
;;   :long "<p>The rules from SystemVerilog-2012:</p>

;; @({
;;      package_scope ::= identifier '::' | '$unit' '::'
;;      ps_class_identifier ::= [ package_scope ] identifier
;; })"
;;   :result (vl-expr-p val)
;;   :resultp-of-nil nil
;;   :fails gracefully
;;   :count strong
;;   (seq tokstream
;;         (when (vl-is-token? :vl-$unit)
;;           (:= (vl-match))
;;           (:= (vl-match-token :vl-scope))
;;           (tail := (vl-match-token :vl-idtoken))
;;           (return
;;            (make-vl-nonatom
;;             :op :vl-scope
;;             :args (list (make-vl-atom :guts (make-vl-keyguts :type :vl-$unit))
;;                         (make-vl-atom :guts (make-vl-hidpiece
;;                                              :name (vl-idtoken->name tail)))))))
;;         (head := (vl-match-token :vl-idtoken))
;;         (when (vl-is-token? :vl-scope)
;;           (:= (vl-match))
;;           (tail := (vl-match-token :vl-idtoken))
;;           (return
;;            (make-vl-nonatom
;;             :op :vl-scope
;;             :args (list (make-vl-atom :guts (make-vl-hidpiece
;;                                              :name (vl-idtoken->name head)))
;;                         (make-vl-atom :guts (make-vl-hidpiece
;;                                              :name (vl-idtoken->name tail)))))))
;;         (return
;;          (make-vl-atom :guts (make-vl-id :name (vl-idtoken->name head)))))
;;   ///
;;   (defthm vl-parse-ps-class-identifier-when-eof
;;     (b* (((mv errmsg ?val ?new-tokens ?new-pstate)
;;           (vl-parse-ps-class-identifier)))
;;       (implies (atom tokens)
;;                errmsg))))


;; (defparser vl-parse-ps-type-identifier ()
;;   :short "Match @('ps_type_identifier'), return an expression."
;;   :long "<p>The rules from SystemVerilog-2012 are:</p>
;; @({
;;      package_scope ::= identifier '::' | '$unit' '::'
;;      ps_type_identifier ::= [ 'local' '::' | package_scope ] identifier
;; })

;; <p>This is equivalent to:</p>
;; @({
;;      ps_type_identifier ::= 'local' '::' identifier
;;                           | ps_class_identifier
;; })"
;;   :result (vl-expr-p val)
;;   :resultp-of-nil nil
;;   :fails gracefully
;;   :count strong
;;   (seq tokstream
;;         (when (vl-is-token? :vl-kwd-local)
;;           (:= (vl-match))
;;           (:= (vl-match-token :vl-scope))
;;           (tail := (vl-match-token :vl-idtoken))
;;           (return
;;            (make-vl-nonatom
;;             :op :vl-scope
;;             :args (list (make-vl-atom :guts (make-vl-keyguts :type :vl-local))
;;                         (make-vl-atom :guts (make-vl-hidpiece
;;                                              :name (vl-idtoken->name tail)))))))
;;         (return-raw
;;          (vl-parse-ps-class-identifier)))
;;   ///
;;   (defthm vl-parse-ps-type-identifier-when-eof
;;     (b* (((mv errmsg ?val ?new-tokens ?new-pstate)
;;           (vl-parse-ps-type-identifier)))
;;       (implies (atom tokens)
;;                errmsg))))








; Increment, Decrement, and Assignment Operators


; expression ::= inc_or_dec_expression
;              | '(' operator_assignment ')'
;
; inc_or_dec_expression ::= inc_or_dec_operator { attribute_instance } variable_lvalue
;                         | variable_lvalue { attribute_instance } inc_or_dec_operator
;
; inc_or_dec_operator ::= '++' | '--'
;
; variable_lvalue ::=
;    [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
;  | { variable_lvalue { , variable_lvalue } }
;  | [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
;  | streaming_concatenation


; operator_assignment ::=


