; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "utils")
(include-book "../../expr")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/coretypes")
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
                           ;; CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P
                           ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP
                           acl2::consp-when-member-equal-of-keyval-alist-p
                           (:t atom)
                           not
                           ;; vl-expr-p-when-member-equal-of-vl-exprlist-p
                           acl2::keyval-alist-p
                           stringp-when-true-listp)))

(define vl-extend-atts-with-linestart ((linestart maybe-natp)
                                       (atts      vl-atts-p))
  :returns (new-atts vl-atts-p)
  (b* ((atts (vl-atts-fix atts))
       ((unless linestart)
        atts)
       (indent (vl-make-index linestart)))
    ;; Most things will start on column 0, or column 1, or column 2, or ...,
    ;; but probably very few things ever start past column 50 or 80, so honsing
    ;; here should achieve very good sharing.
    (mbe :logic (cons (hons "VL_LINESTART" indent)
                      atts)
         :exec (if atts
                   (cons (hons "VL_LINESTART" indent)
                         atts)
                 (hons (hons "VL_LINESTART" indent)
                       atts)))))

(define vl-extend-expr-with-linestart ((linestart maybe-natp)
                                       (expr      vl-expr-p))
  :returns (new-expr vl-expr-p)
  (b* ((expr (vl-expr-fix expr))
       ((unless linestart)
        expr)
       (atts (vl-expr->atts expr))
       (atts (vl-extend-atts-with-linestart linestart atts)))
    (vl-expr-update-atts expr atts)))

(defines vl-expr-has-any-atts-p
  :short "Check whether an expression has any attributes."
  :long "<p>The parser uses this to ensure that we don't encounter any nested
attributes.</p>"

  :flag nil

  (define vl-expr-has-any-atts-p ((x vl-expr-p))
    :parents nil
    :returns (bool booleanp :rule-classes :type-prescription)
    :measure (vl-expr-count x)
    (or (consp (vl-expr->atts x))
        (vl-exprlist-has-any-atts-p (vl-expr->subexprs x))))

  (define vl-exprlist-has-any-atts-p ((x vl-exprlist-p))
    :parents nil
    :returns (bool booleanp :rule-classes :type-prescription)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (or (vl-expr-has-any-atts-p (car x))
          (vl-exprlist-has-any-atts-p (cdr x))))))



(define vl-parse-op-alist-p (arity x)
  (if (atom x)
      (not x)
    (and (consp (car x))
         (vl-tokentype-p (caar x)) ;; token type to match
         (or (and (eql arity 2) (vl-binaryop-p (cdar x)))
             (and (eql arity 1) (vl-unaryop-p (cdar x))))
         (vl-parse-op-alist-p arity (cdr x))))
  ///
  (defthm vl-parse-op-alist-p-when-atom
    (implies (atom x)
             (equal (vl-parse-op-alist-p arity x)
                    (not x))))
  (defthm vl-parse-op-alist-p-when-consp
    (implies (consp x)
             (equal (vl-parse-op-alist-p arity x)
                    (let ((a (car x)) (x (cdr x)))
                      (and (consp a)
                           (vl-tokentype-p (car a))
                           (or (and (eql arity 2) (vl-binaryop-p (cdr a)))
                               (and (eql arity 1) (vl-unaryop-p (cdr a))))
                           (vl-parse-op-alist-p arity x)))))))

(local (defthm vl-tokentype-p-implies-symbolp
         (implies (vl-tokentype-p x)
                  (symbolp x))
         :hints(("Goal" :in-theory (enable vl-tokentype-p)))
         :rule-classes ((:compound-recognizer)
                        (:forward-chaining))))


(defparser vl-parse-op (arity alist)
  :short "Compatible with seq.  Match any of the tokens specified in this
alist, and return the corresponding @(see vl-op-p) for it."
  :long "<p>This helps to avoid many case splits throughout our operator
parsing functions.</p>"
  :guard (vl-parse-op-alist-p arity alist)
  :result (and (implies (equal arity 2)
                        (iff (vl-binaryop-p val) val))
               (implies (equal arity 1)
                        (iff (vl-unaryop-p val) val)))
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
                    vl-parse-op-alist-p-when-consp))


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
                  (and (vl-binaryop-p op)
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
                (vl-binaryop-p y)
                (vl-atts-p z)
                (vl-mixed-binop-list-p w)))))



(define vl-left-associate-mixed-binop-list ((x vl-mixed-binop-list-p))
  :returns (expr vl-expr-p)
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
         (cons (make-vl-binary :op op
                               :left e1
                               :right e2
                               :atts atts)
               rest)))
    (vl-expr-fix (car x)))
  :prepwork ((local (in-theory (enable vl-mixed-binop-list-p)))))



;; (define vl-build-indexing-nest ((expr vl-expr-p)
;;                                 (indices vl-exprlist-p))
;;   :returns (expr vl-expr-p :hyp :fguard)
;;   :short "Build the proper expression for successive indexing operations."
;;   :long "<p>Another operation which we want to left-associate is bit/part
;; selection, which might also be called array or memory indexing.  The idea is
;; that for @('foo[1][2][3]'), we want to build an expression of the form:</p>

;; @({
;;      (vl-index (vl-index (vl-index foo 1)
;;                          2))
;;                3)
;; })

;; <p>This is easy because we are only dealing with one operation and no
;; attributes, so we can just read the list of selects and then left-associate
;; them.</p>"
;;   (if (atom indices)
;;       expr
;;     (vl-build-indexing-nest (make-vl-nonatom :op :vl-index
;;                                              :args (list expr (car indices)))
;;                             (cdr indices)))
;;   :prepwork ((local (in-theory (enable vl-arity-ok-p)))))


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
  ;;   (local (in-theory (enable vl-arity-ok-p)))
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

    (define vl-build-range-select ((name vl-scopeexpr-p)
                                   (indices vl-exprlist-p)
                                   (range vl-erange-p))
      :returns (select-expr vl-expr-p)
      (b* (((vl-erange range) range))
        (case range.type
          (:vl-index
           ;; this is weird and shouldn't happen, but why not
           (make-vl-index :scope name
                          :indices (append-without-guard indices (list range.left))
                          :part (make-vl-partselect-none)))
          (:vl-colon
           (make-vl-index :scope name
                          :indices indices
                          :part (vl-range->partselect
                                 (make-vl-range :msb range.left :lsb range.right))))
          (:vl-pluscolon
           (make-vl-index :scope name
                          :indices indices
                          :part (vl-plusminus->partselect
                                 (make-vl-plusminus :base range.left :width range.right
                                                    :minusp nil))))
          (otherwise
           (make-vl-index :scope name
                          :indices indices
                          :part (vl-plusminus->partselect
                                 (make-vl-plusminus :base range.left :width range.right
                                                    :minusp t)))))))

  (define vl-streamexpr-with ((expr vl-expr-p)
                              (range vl-erange-p))
    :returns (expr-with-range vl-streamexpr-p)
    (b* (((vl-erange range) range))
      (make-vl-streamexpr
       :expr expr
       :part
       (case range.type
         (:vl-index (vl-expr->arrayrange range.left))
         (:vl-colon (vl-range->arrayrange (make-vl-range :msb range.left :lsb range.right)))
         (:vl-pluscolon
          (vl-plusminus->arrayrange (make-vl-plusminus :base range.left :width range.right :minusp nil)))
         (:vl-minuscolon
          (vl-plusminus->arrayrange (make-vl-plusminus :base range.left :width range.right :minusp t))))))))



(define vl-make-guts-from-inttoken ((x vl-inttoken-p))
  :returns (guts vl-value-p)
  :prepwork ((local (defthm consp-of-vl-inttoken-bits
                      (implies (and (vl-inttoken-p x)
                                    (not (vl-inttoken->value x)))
                               (consp (vl-inttoken->bits x)))
                      :hints (("goal" :use vl-inttoken-constraint-p-of-vl-inttoken-parts
                               :in-theory (e/d (vl-inttoken-constraint-p)
                                               (vl-inttoken-constraint-p-of-vl-inttoken-parts)))))))
  (b* (((vl-inttoken x) x))
    (if x.value
        (make-vl-constint :origwidth  x.width
                          :origsign   (if x.signedp :vl-signed :vl-unsigned)
                          :value      x.value
                          :wasunsized x.wasunsized)
      (make-vl-weirdint :origsign   (if x.signedp :vl-signed :vl-unsigned)
                        :bits       (if (mbt (consp x.bits))
                                        x.bits
                                      '(:vl-0val))
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
@('VL_EXPLICIT_PARENS') attribute on non-atoms that have explicit parens.</p>"

  (b* ((atts (vl-expr->atts x))
       (atts (cons (hons "VL_EXPLICIT_PARENS" nil) atts)))
    (vl-expr-update-atts x atts)))

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

       (linestart := (vl-linestart-indent))

       (when (vl-is-token? :vl-inttoken)
         (int := (vl-match))
         (return (make-vl-literal :val (vl-make-guts-from-inttoken int)
                                  :atts (vl-extend-atts-with-linestart linestart nil))))

       (when (vl-is-token? :vl-realtoken)
         (real := (vl-match))
         (return
          (b* ((value (vl-echarlist->string (vl-realtoken->etext real))))
            (make-vl-literal :val (make-vl-real :value value)
                             :atts (vl-extend-atts-with-linestart linestart nil)))))

       (when (vl-is-token? :vl-stringtoken)
         (str := (vl-match))
         (return
          (b* ((value (vl-stringtoken->expansion str)))
            (make-vl-literal :val (make-vl-string :value value)
                             :atts (vl-extend-atts-with-linestart linestart nil)))))

       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         ;; That's it for regular Verilog.
         (return nil))

       ;; New things for SystemVerilog-2012:
       (when (vl-is-token? :vl-extinttoken)
         (ext := (vl-match))
         (return
          (b* ((value (vl-extinttoken->value ext)))
            (make-vl-literal :val (make-vl-extint :value value)
                             :atts (vl-extend-atts-with-linestart linestart nil)))))

       (when (vl-is-token? :vl-timetoken)
         (time := (vl-match))
         (return
          (b* (((vl-timetoken time) time))
            (make-vl-literal :val (make-vl-time :quantity time.quantity
                                                :units time.units)
                             :atts (vl-extend-atts-with-linestart linestart nil)))))

       (when (vl-is-token? :vl-kwd-null)
         (:= (vl-match))
         (return (hons-copy (make-vl-special :key :vl-null
                                             :atts (vl-extend-atts-with-linestart linestart nil)))))

       ;; (when (vl-is-token? :vl-kwd-default)
       ;;   (:= (vl-match))
       ;;   (return (hons-copy (make-vl-atom
       ;;                       :guts (make-vl-keyguts :type :vl-default)))))

       ;; (when (vl-is-token? :vl-kwd-this)
       ;;   (:= (vl-match))
       ;;   (return (hons-copy (make-vl-atom
       ;;                       :guts (make-vl-keyguts :type :vl-this)))))

       (when (vl-is-token? :vl-$)
         (:= (vl-match))
         (return (hons-copy (make-vl-special :key :vl-$
                                             :atts (vl-extend-atts-with-linestart linestart nil)))))

       (return nil))
  ///
  (defthmd tokens-nonempty-when-vl-maybe-parse-base-primary
    (b* (((mv ?errmsg val ?new-tokstream)
          (vl-maybe-parse-base-primary)))
      (implies val (consp (vl-tokstream->tokens))))))


(defval *vl-very-simple-type-table*
  :parents (vl-parse-very-simple-type)
  :showval t
  (b* (((fun (mk typename))
        (b* (((vl-coredatatype-info info) (vl-coretypename->info typename)))
          (cons info.keyword
                (hons-copy (make-vl-coretype :name typename
                                             :signedp info.default-signedp))))))
    (list (mk :vl-byte)
          (mk :vl-shortint)
          (mk :vl-int)
          (mk :vl-longint)
          (mk :vl-integer)
          (mk :vl-time)
          (mk :vl-bit)
          (mk :vl-logic)
          (mk :vl-reg)
          (mk :vl-shortreal)
          (mk :vl-real)
          (mk :vl-realtime))))

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
  :result (vl-datatype-p val)
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

  :result (vl-scopeexpr-p val)
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
          (make-vl-scopeexpr-end
           :hid (make-vl-hidexpr-end :name (vl-idtoken->name head)))))

       (tail := (vl-parse-pva-tail))
       (return
        (make-vl-scopeexpr-colon
         :first (vl-idtoken->name head)
         :rest tail)))
  ///
  (verify-guards vl-parse-pva-tail-fn))

(defparser vl-parse-0+-scope-prefixes ()
  :short "Match @('{ id '::' }') and return a list of all the ids that have been matched."
  :long "<p>See also @(see vl-parse-indexed-id-2012) and @(see vl-scopeexpr).
We use this in the tricky case of parsing:</p>

@({
      { id '::' } hierarchical_identifier select
})

<p>But per our desired scope expression representation, we want to keep all of
the scoping stuff bundled up together, so we prefer to match it first, if it
exists.</p>"
  :verify-guards nil
  :result (string-listp val)
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
        (cons (vl-idtoken->name first)
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

(local (defthm vl-hidname-p-when-stringp
         (implies (stringp x)
                  (vl-hidname-p x))
         :hints(("Goal" :in-theory (enable vl-hidname-p)))))


(define vl-tack-scopes-onto-hid ((scopes vl-scopenamelist-p)
                                 (hid    vl-hidexpr-p))
  :returns (scopeexpr vl-scopeexpr-p)
  (if (atom scopes)
      (make-vl-scopeexpr-end :hid hid)
    (make-vl-scopeexpr-colon
     :first (car scopes)
     :rest (vl-tack-scopes-onto-hid (cdr scopes) hid))))

;; For debugging you may want to comment out functions and add, as a temporary hack:
;; (set-bogus-mutual-recursion-ok t)

(defparser vl-parse-scopename ()
  :result (vl-scopename-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-kwd-local)
         (:= (vl-match))
         (return :vl-local))
       (when (vl-is-token? :vl-$unit)
         (:= (vl-match))
         (return :vl-$unit))
       (id := (vl-match-token :vl-idtoken))
       (return (vl-idtoken->name id))))

(define vl-interpret-expr-as-type ((x vl-expr-p))
  ;; This basically only works if x is a bare scopeexpr.
  :returns (type vl-maybe-datatype-p)
  (vl-expr-case x
    :vl-index (and (atom x.indices)
                   (vl-partselect-case x.part :none)
                   (make-vl-usertype :name x.scope))
    :otherwise nil))


(define vl-plausible-start-of-range-p (&key (tokstream 'tokstream))
  ;; To support sequences/properties: look for a leading open bracket
  ;; but do NOT match things like [*...], [=...] and [->...], which
  ;; are repetitions instead of parts of expressions.
  :enabled t
  (and (vl-is-token? :vl-lbrack)
       (not (vl-lookahead-is-some-token?
             '(:vl-times :vl-arrow :vl-equalsign)
             (cdr (vl-tokstream->tokens))))))

(define vl-initial-patternkey-from-expr ((expr vl-expr-p))
  :returns (key vl-patternkey-p)
  ;; See vl-patternkey and vl-patternkey-ambiguity.  When we parse a simple
  ;; identifier, we want to immediately turn it into a structure member.  This
  ;; might not be quite right: it could also be a type name.  But we can't tell
  ;; that at parse time.  We further disambiguate between structure members and
  ;; types later, when we have enough information about the defined types.
  (if (vl-idexpr-p expr)
      (make-vl-patternkey-structmem :name (vl-idexpr->name expr))
    (make-vl-patternkey-expr :key expr)))

(defparser vl-parse-optional-edge-identifier ()
  :result (vl-evatomtype-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails never
  :count weak
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-posedge
                                  :vl-kwd-negedge
                                  :vl-kwd-edge))
         (edge := (vl-match)))
       (return (if (not edge)
                   :vl-noedge
                 (case (vl-token->type edge)
                   (:vl-kwd-posedge :vl-posedge)
                   (:vl-kwd-negedge :vl-negedge)
                   (:vl-kwd-edge    :vl-edge)
                   (t (impossible)))))))


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
  :ruler-extenders :all
  :measure-debug t
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
          (linestart := (vl-linestart-indent))
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
                (atts (vl-extend-atts-with-linestart linestart atts))
                (tokstream (vl-tokstream-add-warning w)))
             (mv nil atts tokstream)))))

  (defparser vl-parse-1+-expressions-separated-by-commas ()
    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
          (first :s= (vl-parse-expression))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match))
            (rest := (vl-parse-1+-expressions-separated-by-commas)))
          (return (cons first rest))))

  (defparser vl-parse-patternkey ()
    :measure (two-nats-measure (vl-tokstream-measure) 380)
    ;; Very tricky and subtle and ambiguous.  See the documentation for
    ;; vl-patternkey and vl-patternkey-ambiguity.
    (b* (((when (vl-is-token? :vl-kwd-default))
          ;; Unambiguous and nice.
          (seq tokstream
               (:= (vl-match))
               (return (make-vl-patternkey-default))))
         (backup (vl-tokstream-save))

         ((mv err expr tokstream)
          (vl-parse-expression))
         ((unless err)
          (mv err (vl-initial-patternkey-from-expr expr) tokstream))
         (tokstream (vl-tokstream-restore backup)))
      ;; Only other possibility is that it's a core type name which isn't
      ;; a valid expression.
      (seq tokstream
           (type := (vl-parse-simple-type))
           (return (make-vl-patternkey-type :type type)))))

  (defparser vl-parse-1+-keyval-expression-pairs ()
    :measure (two-nats-measure (vl-tokstream-measure) 400)
    (seq tokstream
         (key :s= (vl-parse-patternkey))
         (:= (vl-match-token :vl-colon))
         (val :s= (vl-parse-expression))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-keyval-expression-pairs)))
         (return (cons (cons key val)
                       rest))))

  (defparser vl-parse-expression-without-failure ()
    :measure (two-nats-measure (vl-tokstream-measure) 350)
    (b* ((backup (vl-tokstream-save))
         ((mv err expr tokstream) (vl-parse-expression))
         ((unless err)
          (mv err expr tokstream))
         (tokstream (vl-tokstream-restore backup)))
      (mv nil nil tokstream)))

  (defparser vl-parse-system-function-call ()
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    (seq tokstream
         (linestart := (vl-linestart-indent))
         (fn := (vl-match-token :vl-sysidtoken))
         (when (vl-is-token? :vl-lparen)
           (:= (vl-match))
           (arg1 :w= (vl-parse-expression-without-failure))
           (when (and (not arg1)
                      (not (vl-is-token? :vl-rparen)))
             (typearg :w= (vl-parse-simple-type)))
           (when (vl-is-token? :vl-comma)
              (:= (vl-match))
              (args := (vl-parse-sysfuncall-args)))
           (:= (vl-match-token :vl-rparen)))
         (return
          (let ((fname (vl-sysidtoken->name fn)))
            (make-vl-call
             :name (make-vl-scopeexpr-end :hid (make-vl-hidexpr-end :name fname))
             :typearg typearg
             :plainargs (if arg1 (cons arg1 args) args)
             :systemp t
             :atts (vl-extend-atts-with-linestart linestart nil))))))


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
            (return (make-vl-mintypmax :min min :typ typ :max max)))

          (when (eq (vl-loadconfig->edition config) :verilog-2005)
            (return min))

; Linestart strategy for binary operators.  It's pretty reasonable for someone
; to write either:
;
;    assign foo = (a & b)              // "preferred form"
;               | (b & c);
;
;    assign foo = (a & b) |
;                 (b & c);
;
; So we try to identify linebreaks on *either* side of an operator.  We then
; extend the atts of the expression we create with both linestarts.  How does
; that work?
;
;   Case 1: no linebreaks -- both linestart1 and linestart2 are nil, and (per
;           vl-extend-atts-with-linestart) puts nothing into the attributes.
;
;   Case 2: one linebreak before (preferred form) -- linestart2 is nil and
;           contributes nothing; linestart1 gets recorded as the linestart for
;           this expression which makes sense and agrees with our idea of the
;           preferred form.
;
;   Case 3: one linebreak after (non-preferred form) -- linestart1 is nil and
;           contributes nothing; linestart2 gets recorded as the linestart for
;           this expression.  Effectively this makes the non-preferred form
;           look like it was preferred form, but that still seems pretty good.
;
;   Case 4: two linebreaks -- before and after the operator -- we effectively
;           shadow linestart2 with linestart1, coercing something that is
;           weirdly indented like:
;
;              assign foo = blah
;                         &
;                           blah2
;
;           into the preferred form as if they hadn't written the linebreak
;           after the &.

          (linestart1 := (vl-linestart-indent))
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
          (linestart2 := (vl-linestart-indent))

          (rhs := (vl-parse-expression))
          (return (b* ((atts nil)
                       (atts (vl-extend-atts-with-linestart linestart2 atts))
                       (atts (vl-extend-atts-with-linestart linestart1 atts)))
                    (make-vl-binary :op op
                                    :left min
                                    :right rhs
                                    :atts atts)))))


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
         (linestart := (vl-linestart-indent))
         (:= (vl-match-token :vl-lcurly))
         (args := (vl-parse-1+-expressions-separated-by-commas))
         (:= (vl-match-token :vl-rcurly))
         (return (make-vl-concat :parts args
                                 :atts (vl-extend-atts-with-linestart linestart nil)))))


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
            (return (make-vl-streamexpr :expr expr :part (make-vl-arrayrange-none))))
          (:= (vl-match))
          (:= (vl-match-token :vl-lbrack))
          (range := (vl-parse-range-expression))
          (:= (vl-match-token :vl-rbrack))
          (return (vl-streamexpr-with expr range))))

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
             (make-vl-usertype
              :name
              (make-vl-scopeexpr-colon
               :first :vl-local
               :rest (make-vl-scopeexpr-end :hid (make-vl-hidexpr-end :name (vl-idtoken->name tail)))))))

          (when (vl-is-token? :vl-$unit)
            ;; '$unit' pva_tail
            (:= (vl-match))
            (tail := (vl-parse-pva-tail))
            (return
             (make-vl-usertype
              :name
              (make-vl-scopeexpr-colon
               :first :vl-$unit
               :rest tail))))

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
             (make-vl-usertype
              :name
              (make-vl-scopeexpr-colon
               :first (vl-idtoken->name head)
               :rest tail))))

          ;; identifier | identifier { [ '[' expression ']' ] '.' identifier }
          ;; This is equivalent to hierarchical_identifier, except that we
          ;; can't have $root.  But we don't have to worry about that because
          ;; we know we have an ID, so it can't be root.
          (hid := (vl-parse-hierarchical-identifier nil))

          (return (make-vl-usertype
                   :name (make-vl-scopeexpr-end :hid hid)))))


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
         ((mv err expr tokstream) (vl-parse-expression))
         ((unless err)
          (mv err (make-vl-slicesize-expr :expr expr) tokstream))
         (tokstream (vl-tokstream-restore backup)))
      (seq tokstream
           (type := (vl-parse-simple-type))
           (return (make-vl-slicesize-type :type type)))))

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
         (linestart := (vl-linestart-indent))
         (:= (vl-match-token :vl-lcurly))

         (when (and (vl-is-token? :vl-rcurly) ;; {}
                    (not (eq (vl-loadconfig->edition config) :verilog-2005)))
           (:= (vl-match))
           (return (make-vl-special :key :vl-emptyqueue
                                    :atts (vl-extend-atts-with-linestart linestart nil))))

         (when (and (vl-is-some-token? '(:vl-shl :vl-shr))
                    (not (eq (vl-loadconfig->edition config) :verilog-2005)))
           (op := (vl-match))
           (unless (vl-is-token? :vl-lcurly)
             (slicesize :s= (vl-parse-slice-size)))
           (args := (vl-parse-stream-concatenation))
           (:= (vl-match-token :vl-rcurly))
           (return
            (b* ((dir (vl-token->type op)))
              (make-vl-stream :dir (if (eq dir :vl-shl) :left :right)
                              :size (or slicesize (make-vl-slicesize-none))
                              :parts args
                              :atts (vl-extend-atts-with-linestart linestart nil)))))

         (e1 :s= (vl-parse-expression))

         (when (vl-is-token? :vl-lcurly)
           ;; A multiple concatenation
           (:= (vl-match))
           (parts := (vl-parse-1+-expressions-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-multiconcat :reps e1
                                        :parts parts
                                        :atts (vl-extend-atts-with-linestart linestart nil))))

         ;; Otherwise, a regular concat -- does it have extra args?
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-expressions-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-concat :parts (cons e1 rest)
                                   :atts (vl-extend-atts-with-linestart linestart nil))))

         ;; Nope, just a concat of one expression.
         (:= (vl-match-token :vl-rcurly))
         (return (make-vl-concat :parts (list e1)
                                 :atts (vl-extend-atts-with-linestart linestart nil)))))




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
               (make-vl-hidexpr-dot
                :first (make-vl-hidindex :name :vl-$root)
                :rest tail)))

            (id := (vl-match-token :vl-idtoken))

            (when (vl-is-token? :vl-dot)
              (:= (vl-match))
              (tail :s= (vl-parse-hierarchical-identifier t))
              (return
               (make-vl-hidexpr-dot
                :first (make-vl-hidindex :name (vl-idtoken->name id))
                :rest tail)))

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
                 (make-vl-hidexpr-dot
                  :first (make-vl-hidindex :name (vl-idtoken->name id)
                                           :indices (list expr))
                  :rest tail)))

              ;; Else, found some stray bracket but not a good expr part.
              (return (make-vl-hidexpr-end :name (vl-idtoken->name id))))

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
               (make-vl-hidexpr-dot
                :first (make-vl-hidindex :name (vl-idtoken->name id)
                                         :indices exprs)
                :rest tail)))

            ;; Else, found some stray bracket that isn't ours
            (return
             (make-vl-hidexpr-end :name (vl-idtoken->name id))))))

; function_call ::=
;    hierarchical_identifier { attribute_instance }
;      '(' expression { ',' expression } ')'

  (defparser vl-parse-scoped-hid ()
    :measure (two-nats-measure (vl-tokstream-measure) 5)
    ;; If we have a name followed by ::, then it's part of the scope, otherwise
    ;; it's part of the hid.  BOZO This is a bit too permissive with nesting.
    (b* ((backup (vl-tokstream-save))
         ((mv err first tokstream)
          (seq tokstream
               (name := (vl-parse-scopename))
               (:= (vl-match-token :vl-scope))
               (return name)))
         ((when err)
          (b* ((tokstream (vl-tokstream-restore backup)))
            (seq tokstream
                 (hid := (vl-parse-hierarchical-identifier nil))
                 (return (make-vl-scopeexpr-end :hid hid))))))
      (seq tokstream
           (rest := (vl-parse-scoped-hid))
           (return (make-vl-scopeexpr-colon :first first :rest rest)))))

  (defparser vl-parse-call-namedarg-pair ()
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
         (:= (vl-match-token :vl-dot))
         (id := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-lparen))
         (unless (vl-is-token? :vl-rparen)
           (expr :s= (vl-parse-expression)))
         (:= (vl-match-token :vl-rparen))
         (return (cons (vl-idtoken->name id) expr))))

  (defparser vl-parse-call-namedargs-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
         (unless (vl-is-token? :vl-comma)
           (return nil))
         (:= (vl-match)) ;; comma
         (pair :s= (vl-parse-call-namedarg-pair))
         (rest := (vl-parse-call-namedargs-aux))
         (return (cons pair rest))))

  (defparser vl-parse-call-namedargs ()
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    (seq tokstream
         (when (vl-is-token? :vl-rparen)
           (return nil))
         (pair :s= (vl-parse-call-namedarg-pair))
         (rest := (vl-parse-call-namedargs-aux))
         (return (cons pair rest))))

  (defparser vl-parse-call-plainargs-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
         (unless (vl-is-token? :vl-comma)
           (return nil))
         (:= (vl-match)) ;; comma
         (when (vl-is-token? :vl-rparen)
           ;; Verilog tools seem to allow syntax like:
           ;;    myfun(a,b,); <-- note the additional , here.
           ;; This seems to get interpreted as a "blank" argument for the purposes of arity checking,
           ;; so go ahead and return a unary list here instead of just nil.
           (return (list nil)))
         (when (vl-is-token? :vl-dot)
           ;; go to namedargs
           (return nil))
         (unless (vl-is-token? :vl-comma)
           (expr :s= (vl-parse-expression)))
         (rest := (vl-parse-call-plainargs-aux))
         (return (cons expr rest))))

  (defparser vl-parse-call-plainargs ()
    :measure (two-nats-measure (vl-tokstream-measure) 1000)
    (seq tokstream
         (when (vl-is-token? :vl-dot)
           (return nil))
         (unless (vl-is-token? :vl-comma)
           (expr :s= (vl-parse-expression)))
         (rest := (vl-parse-call-plainargs-aux))
         (return (cons expr rest))))

  (defparser vl-parse-function-call ()
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
         (linestart := (vl-linestart-indent))
         (id :s= (vl-parse-scoped-hid))
         (atts :w= (vl-parse-0+-attribute-instances))
         (:= (vl-match-token :vl-lparen))

         (when (and (not (eq (vl-loadconfig->edition config) :verilog-2005))
                    (vl-is-token? :vl-rparen))
           ;; SystemVerilog-2012 extension: function calls can now have no
           ;; arguments at all.  They can also have other fancy
           ;; list_of_arguments stuff, like named argument lists, but I'm not
           ;; going to try to support that yet.
           (:= (vl-match-token :vl-rparen))
           (return (make-vl-call :name id
                                 :systemp nil
                                 :atts (vl-extend-atts-with-linestart linestart atts))))

         (plainargs :w= (vl-parse-call-plainargs))
         (namedargs :w= (vl-parse-call-namedargs))
         (:= (vl-match-token :vl-rparen))
         (return
          (make-vl-call :name id
                        :plainargs plainargs
                        :namedargs namedargs
                        :systemp nil
                        :atts (vl-extend-atts-with-linestart linestart atts)))))

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
    (b* (((unless (vl-plausible-start-of-range-p))
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
    :guard (vl-scopenamelist-p scopes)
    (seq tokstream
         (hid :s= (vl-parse-hierarchical-identifier recursivep))
         (bexprs :w= (vl-parse-0+-bracketed-expressions))
         (when (vl-plausible-start-of-range-p)
           (:= (vl-match))
           (range := (vl-parse-range-expression))
           (:= (vl-match-token :vl-rbrack)))
         (return
          (let* ((ans (vl-tack-scopes-onto-hid scopes hid)))
            (if range
                (vl-build-range-select ans bexprs range)
              (make-vl-index :scope ans
                             :indices bexprs
                             :part (make-vl-partselect-none)))))))

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
                                              (:vl-kwd-local :vl-local)
                                              (:vl-$unit     :vl-$unit))
                                            morescopes)
                                      t)))
         (scopes := (vl-parse-0+-scope-prefixes))
         (return-raw
          (vl-parse-indexed-id-2005 scopes (consp scopes)))))

  (defparser vl-parse-indexed-id ()
    :measure (two-nats-measure (vl-tokstream-measure) 13)
    (seq tokstream
         (linestart := (vl-linestart-indent))
         (ans := (if (eq (vl-loadconfig->edition config) :verilog-2005)
                     (vl-parse-indexed-id-2005 nil nil)
                   (vl-parse-indexed-id-2012)))
         (return (vl-extend-expr-with-linestart linestart ans))))

  (defparser vl-parse-assignment-pattern ()
    :measure (two-nats-measure (vl-tokstream-measure) 500)
    ;; (declare (xargs :measure-debug t))
    ;; We've parsed the initial '{ and need to figure out which form it is.  To
    ;; do that, we parse a patternkey (which is more general than an expression).

    ;; If we get an expression, then the next token will determine what kind of
    ;; assignment pattern we have:
    ;;  rcurly -> positional pattern (with only 1 elt)
    ;;  comma -> positional pattern
    ;;  colon -> key/value pattern
    ;;  lcurly -> multiconcat pattern.
    ;; If it's a type or default, then we'd better have a key/value pattern
    (b* ((backup (vl-tokstream-save))
         ;; We do this in a convoluted manner rather than just parsing a
         ;; patternkey because we want to capture the error message from
         ;; parsing the first element as an expression.
         ((mv expr-err first-expr tokstream)
          (seq tokstream
               (expr :w= (vl-parse-expression))
               (return expr)))
         ((mv err first-key tokstream)
          (if expr-err
              (b* ((tokstream (vl-tokstream-restore backup)))
                (seq tokstream
                     (key :w= (vl-parse-patternkey))
                     (return key)))
            (mv nil (vl-initial-patternkey-from-expr first-expr) tokstream)))
         ((when err) (mv err nil tokstream)))
      (seq tokstream
           (when (vl-is-token? :vl-colon)
             ;; Key/val pattern.  First is really a patternkey and we don't care what kind.
             (:= (vl-match))
             (firstval :s= (vl-parse-expression))
             (when (vl-is-token? :vl-rcurly)
               (:= (vl-match))
               ;; just one key/val pair
               (return (make-vl-assignpat-keyval
                        :pairs (list (cons first-key firstval)))))
             ;; otherwise, better be a comma and then more key/values
             (:= (vl-match-token :vl-comma))
             (rest := (vl-parse-1+-keyval-expression-pairs))
             (:= (vl-match-token :vl-rcurly))
             (return (make-vl-assignpat-keyval
                      :pairs (cons (cons first-key firstval)
                                   rest))))

           ;; Otherwise, we don't actually have key/val pairs, so first better
           ;; just be an expression.
           (when expr-err
             (return-raw (mv expr-err nil tokstream)))

           (when (vl-is-token? :vl-rcurly) ;; positional, only 1 element
             (:= (vl-match))
             (return (make-vl-assignpat-positional :vals (list first-expr))))

           (when (vl-is-token? :vl-comma)
             ;; positional
             (:= (vl-match))
             (rest := (vl-parse-1+-expressions-separated-by-commas))
             (:= (vl-match-token :vl-rcurly))
             (return (make-vl-assignpat-positional :vals (cons first-expr rest))))

           ;; Otherwise, better be an lcurly, and we have a multiconcat.
           (:= (vl-match-token :vl-lcurly))
           (parts := (vl-parse-1+-expressions-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (:= (vl-match-token :vl-rcurly))

           (return (make-vl-assignpat-repeat :reps first-expr
                                             :vals parts)))))



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
          ;; BOZO maybe think more about how to handle linestart here.
          (seq tokstream
                (:= (vl-match))
                (expr := (vl-parse-mintypmax-expression))
                (:= (vl-match-token :vl-rparen))
                (return (vl-mark-as-explicit-parens expr))))

         ((when (eq type :vl-quote))
          (seq tokstream
               (linestart := (vl-linestart-indent))
               (:= (vl-match))
               (:= (vl-match-token :vl-lcurly))
               ;; Assignment pattern with no type cast.
               (pat := (vl-parse-assignment-pattern))
               (return (make-vl-pattern :pat pat :atts (vl-extend-atts-with-linestart linestart nil))))))

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
          ;; I don't think we want to bother looking for linestarts here because
          ;; it would be weird to break foo'(bar) across lines at the quote.
          (when (vl-is-token? :vl-quote)
            (:= (vl-match))
            (when (vl-is-token? :vl-lparen)
              ;; Cast expression.
              (:= (vl-match))
              (arg := (vl-parse-expression))
              (:= (vl-match-token :vl-rparen))
              (return (make-vl-cast :to (make-vl-casttype-size :size primary)
                                    :expr arg)))
            ;; otherwise, better be a typed assignment pattern, and we need to
            ;; be able to reinterpret primary as a type:
            (:= (vl-match-token :vl-lcurly))
            (pattern := (vl-parse-assignment-pattern))
            (return-raw
             (b* ((type (vl-interpret-expr-as-type primary))
                  ((unless type)
                   (vl-parse-error "Couldn't interpret cast expression as datatype.")))
               (mv nil (make-vl-pattern :pattype type :pat pattern) tokstream))))
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
                                  (:vl-kwd-signed   (make-vl-casttype-signedness :signedp t))
                                  (:vl-kwd-unsigned   (make-vl-casttype-signedness :signedp nil))
                                  (:vl-kwd-string   (make-vl-casttype-type :type (make-vl-coretype :name :vl-string))) ;; Is this at all correct?
                                  (:vl-kwd-const    (make-vl-casttype-const)))))
               (make-vl-cast :to casting-type
                             :expr arg))))

          ;; Otherwise, better be a simple-type.
          (type :s= (vl-parse-simple-type))
          (:= (vl-match-token :vl-quote))
          (:= (vl-match-token :vl-lparen))
          (arg := (vl-parse-expression))
          (:= (vl-match-token :vl-rparen))
          (return (make-vl-cast :to (make-vl-casttype-type :type type)
                                :expr arg))))

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


    ;; Unary operators aren't supposed to be nested without parens, even in
    ;; SystemVerilog.  However, in practice many implementations support
    ;; certain nestings such as ! | a, ~ | a.  The pattern for VCS, at least,
    ;; seems to be that lognot/bitnot allow another unary op inside, whereas
    ;; others don't.
    (seq tokstream

; For a unary operator I think it makes sense to only to look for a linestart
; before the operator.  It's of course legal to write something like
;
;      assign foo = |
;                   bar;
;
; But that's really weird and not anything we'd want to pretty-print.  In fact,
; hell, that might even be worth warning about.  We could stick in an attribute,
; I guess... "some day."

         (linestart := (vl-linestart-indent))
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
           ;; increment operators in that case.  See failtest/inc15c.v.
           (return-raw
            (b* ((backup (vl-tokstream-save))
                 ((mv err val tokstream)
                  (seq tokstream
                       (atts := (vl-parse-0+-attribute-instances))
                       (post := (vl-parse-op 1 '((:vl-plusplus   . :vl-unary-postinc)
                                                 (:vl-minusminus . :vl-unary-postdec))))
                       (unless post
                         (return nil))

                       (return (make-vl-unary :op post :arg primary :atts atts))))
                 ((when (and (not err) val))
                  (mv nil val tokstream))
                 (tokstream (vl-tokstream-restore backup)))
              (mv nil primary tokstream))))

          (atts :w= (vl-parse-0+-attribute-instances))
          (primary := (if (member-eq op '(:vl-unary-lognot :vl-unary-bitnot))
                          (vl-parse-unary-expression)
                        (vl-parse-primary)))

          ;; We had a prefix unary-operator, so we don't need to try to handle
          ;; post-increment/decrement operators here, because no matter what
          ;; the prefix was, it isn't a valid lvalue.  That is, it's malformed
          ;; to try to write stuff like (|a)++ or (++a)++.  See also
          ;; failtest/inc15.v and failtest/inc15b.v.
          (return (make-vl-unary :op   op
                                 :atts (vl-extend-atts-with-linestart linestart atts)
                                 :arg  primary))))


; power_expression ::=
;    unary_expression { '**' { attribute_instance } unary_expression }

  (defparser vl-parse-power-expression-aux ()
    :measure (two-nats-measure (vl-tokstream-measure) 60)
    (seq tokstream
          (first :s= (vl-parse-unary-expression))
          (unless (vl-is-token? :vl-power)
            (return (list first)))
          (linestart1 := (vl-linestart-indent))
          (:= (vl-match))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-power-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first :vl-binary-power atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-times . :vl-binary-times)
                                  (:vl-div   . :vl-binary-div)
                                  (:vl-rem   . :vl-binary-rem))))
          (unless op
            (return (list first)))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-mult-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first op atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-plus  . :vl-binary-plus)
                                  (:vl-minus . :vl-binary-minus))))
          (unless op
            (return (list first)))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-add-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first op atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-shl  . :vl-binary-shl)
                                  (:vl-shr  . :vl-binary-shr)
                                  (:vl-ashl . :vl-binary-ashl)
                                  (:vl-ashr . :vl-binary-ashr))))
          (unless op
            (return (list first)))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-shift-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first op atts tail)))))

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
          (when (vl-is-token? :vl-kwd-inside)
            (linestart1 := (vl-linestart-indent))
            (:= (vl-match))
            (linestart2 := (vl-linestart-indent))
            ;; Inside operators are special because the second argument is
            ;; a value range list.
            (:= (vl-match-token :vl-lcurly))
            (set := (vl-parse-1+-open-value-ranges))
            (:= (vl-match-token :vl-rcurly))
            (return (b* ((atts nil)
                         (atts (vl-extend-atts-with-linestart linestart2 atts))
                         (atts (vl-extend-atts-with-linestart linestart1 atts)))
                      (list (make-vl-inside :elem first :set set :atts atts)))))

          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-lt  . :vl-binary-lt)
                                  (:vl-lte . :vl-binary-lte)
                                  (:vl-gt  . :vl-binary-gt)
                                  (:vl-gte . :vl-binary-gte))))
          (unless op
            (return (list first)))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-compare-expression-aux))
          (return (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                       (atts (vl-extend-atts-with-linestart linestart1 atts)))
                    (list* first op atts tail)))))

  (defparser vl-parse-compare-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 150)
    (seq tokstream
          (mixed := (vl-parse-compare-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))

  (defparser vl-parse-open-value-range ()
    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
         (when (vl-plausible-start-of-range-p)
           ;; We want [ low : high ] here
           (:= (vl-match))
           (low :w= (vl-parse-expression))
           (:= (vl-match-token :vl-colon))
           (high := (vl-parse-expression))
           (:= (vl-match-token :vl-rbrack))
           (return (make-vl-valuerange-range :low low :high high)))
         ;; Otherwise, just an expression
         (expr := (vl-parse-expression))
         (return (make-vl-valuerange-single :expr expr))))


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
          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-eq      . :vl-binary-eq)
                                  (:vl-neq     . :vl-binary-neq)
                                  (:vl-ceq     . :vl-binary-ceq)
                                  (:vl-cne     . :vl-binary-cne)
                                  (:vl-wildeq  . :vl-binary-wildeq)
                                  (:vl-wildneq . :vl-binary-wildneq))))
          (unless op
            (return (list first)))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-equality-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first op atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (:= (vl-match))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitand-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first :vl-binary-bitand atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-xor . :vl-binary-xor)
                                  (:vl-xnor . :vl-binary-xnor))))
          (linestart2 := (vl-linestart-indent))
          (unless op
            (return (list first)))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitxor-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first op atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (:= (vl-match))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitor-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first :vl-binary-bitor atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (:= (vl-match))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-logand-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first :vl-binary-logand atts tail)))))

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
          (linestart1 := (vl-linestart-indent))
          (:= (vl-match))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-logor-expression-aux))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (list* first :vl-binary-logor atts tail)))))

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

; Linestart strategy for ?: operators
;
; This is more complex than for binary operators because there are two operator
; tokens.  A designer might put a newline:
;
;   - on either side of the ? character
;   - on either side of the : character
;
; Let's look at some examples of different styles.  Probably more often we
; will encounter newlines at the colons, e.g.,:
;
;    assign foo = a1 ? b1        // "preferred form"
;               : a2 ? b2
;               : b3;
;
;    assign foo = a1 ? b1 :
;                 a2 ? b2 :
;                 b3;
;
; Another possibility is that we will have newlines around the question marks,
; which might make look nice if the test expression is long, e.g.,
;
;    assign foo = (foo == bar && bass == 0)        // "preferred form"
;                   ? b1 + x + y
;                   : b2 + x + y;
;
;    assign foo = (foo == bar && baz == 0) ?
;                      b1 + x + y
;                  : b2 + x + y;
;
; Our strategy will basically be like the strategy for binary operators.  We
; will recognize newlines on either side of ? and :, and if there are newlines
; on both sides, we'll collapse them as with binary operators so that the
; pre-token linestart is the one that gets recorded.  Our pretty-printer will
; translate the above into the preferred forms, where the : and ? operators
; come at the start of the subsequent line.

          (qmark-linestart1 := (vl-linestart-indent))
          (:= (vl-match))
          (qmark-linestart2 := (vl-linestart-indent))

          (atts :w= (vl-parse-0+-attribute-instances))
          ;; Subtle!.  The middle expression needs to not be just a
          ;; qmark_expression, because that wouldn't match lower-precedence
          ;; things, e.g., for 1 ? 2 -> 3 : 4 to work, we need the middle
          ;; expression to be an arbitrary expression.
          (second :s= (vl-parse-expression))

          (colon-linestart1 := (vl-linestart-indent))
          (:= (vl-match-token :vl-colon))
          (colon-linestart2 := (vl-linestart-indent))

          ;; Subtle!  The third expression needs to ONLY be a qmark expression.
          ;; We don't want to match, e.g., the 3->4 part of 1 ? 2 : 3->4,
          ;; because the -> has lower precedence than the ?:, so we need to
          ;; treat that as (1?2:3) -> 4 instead.
          (third := (vl-parse-qmark-expression))
          (return
           (b* ((qmark-linestart (or qmark-linestart1 qmark-linestart2))
                (colon-linestart (or colon-linestart1 colon-linestart2))
                ;; See also vl-extend-atts-with-linestart for comments on why
                ;; we use HONS here.
                (atts (if qmark-linestart
                          (cons (hons "VL_QMARK_LINESTART" (vl-make-index qmark-linestart))
                                atts)
                        atts))
                (atts (if colon-linestart
                          (cons (hons "VL_COLON_LINESTART" (vl-make-index colon-linestart))
                                atts)
                        atts)))
             (make-vl-qmark :test first
                            :then second
                            :else third
                            :atts atts)))))

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
          (linestart1 := (vl-linestart-indent))
          (op := (vl-parse-op 2 '((:vl-arrow . :vl-implies)
                                  (:vl-equiv . :vl-equiv))))
          (unless op
            (return first))
          (linestart2 := (vl-linestart-indent))
          (atts :w= (vl-parse-0+-attribute-instances))
          (second :s= (vl-parse-impl-expression))
          (return
           (b* ((atts (vl-extend-atts-with-linestart linestart2 atts))
                (atts (vl-extend-atts-with-linestart linestart1 atts)))
             (make-vl-binary :op op
                             :left first
                             :right second
                             :atts atts)))))



; Event Expressions
;
; Verilog-2005:
;
; event_expression ::=
;    expression
;  | 'posedge' expression
;  | 'negedge' expression
;  | event_expression 'or' event_expression
;  | event_expression ',' event_expression
;
; SystemVerilog-2012:
;
; event_expression ::=
;     [edge_identifier] expression [ 'iff' expression]
;   | sequence_instance [ 'iff' expression ]
;   | event_expression 'or' event_expression
;   | event_expression ',' event_expression
;   | '(' event_expression ')'
;
; We don't yet handle the IFF expressions or sequence_instance things here.
; Handling sequence_instance would require making this mutually recursive with
; sequences, which are a godawful mess.

  (defparser vl-parse-event-expression-2005 ()
    ;; Returns an evatomlist
    :measure (two-nats-measure (vl-tokstream-measure) 310) ; can call vl-parse-expression without consuming any tokens
    (seq tokstream
         (when (vl-is-some-token? '(:vl-kwd-posedge :vl-kwd-negedge))
           (edge := (vl-match)))
         (expr :s= (vl-parse-expression))
         (when (vl-is-some-token? '(:vl-kwd-or :vl-comma))
           (:= (vl-match))
           (rest := (vl-parse-event-expression-2005)))
         (return
          (let ((edgetype (if (not edge)
                              :vl-noedge
                            (case (vl-token->type edge)
                              (:vl-kwd-posedge :vl-posedge)
                              (:vl-kwd-negedge :vl-negedge)
                              (t (impossible))))))
            (cons (make-vl-evatom :type edgetype
                                  :expr expr)
                  rest)))))

  (defparser vl-parse-event-expression-2012 ()
    ;; Returns an evatomlist
    :measure (two-nats-measure (vl-tokstream-measure) 310) ; can call vl-parse-expression without consuming any tokens
    (seq tokstream

         (when (vl-is-token? :vl-lparen)
           ;; SystemVerilog-2012 adds support for arbitrary paren nesting here.
           (:= (vl-match))
           (nested :w= (vl-parse-event-expression-2012))
           (:= (vl-match-token :vl-rparen))
           ;; BUGFIX 2017-04-20.  We used to (return subexpr) here.  That
           ;; is good enough for simple cases of extra parentheses, like
           ;;
           ;;    always @((posedge foo))
           ;;
           ;; but it doesn't correctly parse the rest of the event expression
           ;; when there are things like
           ;;
           ;;    always @(((posedge foo)) or ((posedge bar)))
           ;;
           ;; or similar.  To handle those, we don't return here but instead fall
           ;; through to the rest of the function, and flatten the subexpr into
           ;; the list as we go.
           )

         (unless nested
           (edge :w= (vl-parse-optional-edge-identifier))
           (expr :s= (vl-parse-expression)))

         (when (vl-is-token? :vl-kwd-iff)
           ;; We don't have anywhere in our parse tree structures yet to put the
           ;; IFF part yet.
           (return-raw
            (vl-parse-error "BOZO need to implement event_expressions with 'iff' clauses.")))
         (when (vl-is-some-token? '(:vl-kwd-or :vl-comma))
           (:= (vl-match))
           (rest := (vl-parse-event-expression-2012)))
         (return (if nested
                     (append-without-guard nested rest)
                   (cons (make-vl-evatom :type edge
                                         :expr expr)
                         rest)))))

  (defparser vl-parse-event-expression ()
    ;; Returns an evatomlist
    :measure (two-nats-measure (vl-tokstream-measure) 320)
    (seq tokstream
         (when (eq (vl-loadconfig->edition config) :verilog-2005)
           (ret := (vl-parse-event-expression-2005))
           (return ret))
         (ret := (vl-parse-event-expression-2012))
         (return ret)))

; clocking_event ::= '@' identifier
;                  | '@' '(' event_expression ')'

  (defparser vl-parse-clocking-event ()
    ;; Returns an evatomlist
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
         (:= (vl-match-token :vl-atsign))
         (when (vl-is-token? :vl-idtoken)
           (id := (vl-match))
           (return (list (make-vl-evatom :type :vl-noedge
                                         :expr (vl-idexpr (vl-idtoken->name id))))))
         (:= (vl-match-token :vl-lparen))
         (evatoms := (vl-parse-event-expression))
         (:= (vl-match-token :vl-rparen))
         (return evatoms)))

; system_function_call ::=
;    system_identifier [ '(' expression { ',' expression } ')' ]
;
; Strangely, system calls are not allowed to have attributes even though
; regular function calls are allowed to.
;
; The alleged grammar, above, is a lie, for two reasons.
;
; 1. There are certain system calls such as $rose, $fell, etc., described in
;    the SystemVerilog-2012 standard, which can take clocking events as
;    arguments, and clocking events are not expressions.  To support this, we
;    allow clocking events to become vl-eventexpr expressions.
;
; 2. Commercial tools allow for blank arguments to functions like $display, so
;    we need to make the expressions above optional.

  (defparser vl-parse-expr-or-clocking-event ()
    ;; Returns a vl-expr-p, possibly a vl-eventexpr.  Matches either an
    ;; expression or a clocking_event like @(posedge clock).
    :measure (two-nats-measure (vl-tokstream-measure) 310)
    (seq tokstream
         (when (vl-is-token? :vl-atsign)
           (evatoms := (vl-parse-clocking-event))
           (return (make-vl-eventexpr :atoms evatoms
                                      :atts nil)))
         (expr := (vl-parse-expression))
         (return expr)))

  (defparser vl-parse-sysfuncall-args ()
    ;; Returns a vl-maybe-exprlist-p
    :measure (two-nats-measure (vl-tokstream-measure) 320)
    (seq tokstream
         (when (vl-is-token? :vl-rparen)
           (return nil))

         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-sysfuncall-args))
           (return (cons nil rest)))

         (first :s= (vl-parse-expr-or-clocking-event))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-sysfuncall-args)))
         (return (cons first rest))))

  (defparser vl-parse-expression ()
    :measure (two-nats-measure (vl-tokstream-measure) 300)
    (seq tokstream
          (unless (and (vl-is-token? :vl-kwd-tagged)
                       (not (eq (vl-loadconfig->edition config) :verilog-2005)))
            (expr :s= (vl-parse-impl-expression))
            (return expr))

          ;; tagged_union_expression ::= tagged id [expression]
          (linestart := (vl-linestart-indent))
          (:= (vl-match))
          (id := (vl-match-token :vl-idtoken))
          (return-raw
           (b* ((tag     (vl-idtoken->name id))
                (atts    (vl-extend-atts-with-linestart linestart nil))
                (backup  (vl-tokstream-save))
                ((mv err expr tokstream)
                 (seq tokstream
                       (expr :s= (vl-parse-expression))
                       (return expr)))
                ((when err)
                 ;; No subsequent expression is fine.
                 (b* ((tokstream (vl-tokstream-restore backup)))
                   (mv nil (make-vl-tagged :tag tag :atts atts) tokstream)))

                ;; Well, what a nightmare.  This is completely ambiguous, and
                ;; VCS/NCVerilog don't implement it yet, so there's no way to
                ;; test what commercial simulators do.  Well-played, IEEE.  The
                ;; following is totally gross, but maybe sort of reasonable?
                ;; Maybe we can rework it, if this ever gets straightened out.
                ((unless (or (hons-assoc-equal "VL_EXPLICIT_PARENS"
                                               (vl-expr->atts expr))
                             (vl-expr-case expr
                               :vl-binary nil
                               :vl-qmark nil
                               :otherwise t)))
                 (vl-parse-error
                  "Cowardly refusing to support tagged union expression such as
                   'tagged foo 1 + 2' due to unclear precedence.  Workaround:
                   add explicit parens, e.g., write 'tagged foo (1 + 2)'
                   instead."))

                (ans (make-vl-tagged :tag tag :expr expr :atts atts)))
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
        ,(vl-val-when-error-claim vl-parse-event-expression-2005)
        ,(vl-val-when-error-claim vl-parse-event-expression-2012)
        ,(vl-val-when-error-claim vl-parse-event-expression)
        ,(vl-val-when-error-claim vl-parse-clocking-event)
        ,(vl-val-when-error-claim vl-parse-expr-or-clocking-event)
        ,(vl-val-when-error-claim vl-parse-sysfuncall-args)
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
        ,(vl-val-when-error-claim vl-parse-call-namedarg-pair)
        ,(vl-val-when-error-claim vl-parse-call-namedargs-aux)
        ,(vl-val-when-error-claim vl-parse-call-namedargs)
        ,(vl-val-when-error-claim vl-parse-call-plainargs-aux)
        ,(vl-val-when-error-claim vl-parse-call-plainargs)
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
        ,(vl-val-when-error-claim vl-parse-patternkey)
        ,(vl-val-when-error-claim vl-parse-expression-without-failure)
        ,(vl-val-when-error-claim vl-parse-scoped-hid)
        ,(vl-val-when-error-claim vl-parse-expression)
        :hints(
               ;; Baseline: 8.91 seconds
               ;; (and acl2::stable-under-simplificationp
               ;;      (flag::expand-calls-computed-hint
               ;;       acl2::clause
               ;;       ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))
               ;; New: 8.58 seconds
               (and acl2::stable-under-simplificationp
                    (expand-only-the-flag-function-hint clause state)))))))



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
        ,(vl-warning-claim vl-parse-event-expression-2005)
        ,(vl-warning-claim vl-parse-event-expression-2012)
        ,(vl-warning-claim vl-parse-event-expression)
        ,(vl-warning-claim vl-parse-clocking-event)
        ,(vl-warning-claim vl-parse-expr-or-clocking-event)
        ,(vl-warning-claim vl-parse-sysfuncall-args)
        ,(vl-warning-claim vl-parse-call-namedarg-pair)
        ,(vl-warning-claim vl-parse-call-namedargs-aux)
        ,(vl-warning-claim vl-parse-call-namedargs)
        ,(vl-warning-claim vl-parse-call-plainargs-aux)
        ,(vl-warning-claim vl-parse-call-plainargs)
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
        ,(vl-warning-claim vl-parse-patternkey)
        ,(vl-warning-claim vl-parse-expression-without-failure)
        ,(vl-warning-claim vl-parse-scoped-hid)
        ,(vl-warning-claim vl-parse-expression)
        :hints(;; Baseline: 7.85 seconds
               ;; (and acl2::stable-under-simplificationp
               ;;      (flag::expand-calls-computed-hint
               ;;       acl2::clause
               ;;       ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))
               ;; New: 7.66 seconds
               (and acl2::stable-under-simplificationp
                    (expand-only-the-flag-function-hint clause state))
               )))))



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

(local (defthm consp-of-tokens-when-is-token
         (implies (vl-is-token? type)
                  (consp (vl-tokstream->tokens)))
         :rule-classes :forward-chaining))

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
      ,(vl-progress-claim vl-parse-event-expression-2005)
      ,(vl-progress-claim vl-parse-event-expression-2012)
      ,(vl-progress-claim vl-parse-event-expression)
      ,(vl-progress-claim vl-parse-clocking-event)
      ,(vl-progress-claim vl-parse-expr-or-clocking-event)
      ,(vl-progress-claim vl-parse-sysfuncall-args :strongp nil)
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
      ,(vl-progress-claim vl-parse-call-namedarg-pair)
      ,(vl-progress-claim vl-parse-call-namedargs-aux :strongp nil)
      ,(vl-progress-claim vl-parse-call-namedargs :strongp nil)
      ,(vl-progress-claim vl-parse-call-plainargs-aux :strongp nil)
      ,(vl-progress-claim vl-parse-call-plainargs :strongp nil)
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
      ,(vl-progress-claim vl-parse-patternkey ;; :strongp nil
                          )
      ,(vl-progress-claim vl-parse-expression-without-failure :strongp nil)
      ,(vl-progress-claim vl-parse-scoped-hid)
      ,(vl-progress-claim vl-parse-expression)
      :hints(;; baseline: 17.63 seconds
             (and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))
             ;; new: 17.66 seconds
             ;; (and acl2::stable-under-simplificationp
             ;;      (expand-only-the-flag-function-hint clause state))
             )))))

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

(local (defthm is-token?-when-empty
         (implies (not (consp (vl-tokstream->tokens)))
                  (not (vl-is-token? type)))
         :hints(("Goal" :in-theory (enable vl-is-token?)))))

(local (defthm atom-of-tokens-when-atom-of-earlier-tokens
         (implies (and (not (consp (vl-tokstream->tokens)))
                       (<= (len (vl-tokstream->tokens
                                 :tokstream res))
                           (len (vl-tokstream->tokens))))
                  (not (consp (vl-tokstream->tokens
                                 :tokstream res))))))

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
        ,(vl-eof-claim vl-parse-event-expression-2005 :error)
        ,(vl-eof-claim vl-parse-event-expression-2012 :error)
        ,(vl-eof-claim vl-parse-event-expression :error)
        ,(vl-eof-claim vl-parse-clocking-event :error)
        ,(vl-eof-claim vl-parse-expr-or-clocking-event :error)
        ,(vl-eof-claim vl-parse-sysfuncall-args :error)
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
        ,(vl-eof-claim vl-parse-call-namedarg-pair :error)
        ,(vl-eof-claim vl-parse-call-namedargs-aux nil)
        ,(vl-eof-claim vl-parse-call-namedargs :error)
        ,(vl-eof-claim vl-parse-call-plainargs-aux nil)
        ,(vl-eof-claim vl-parse-call-plainargs :error)
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
        ,(vl-eof-claim vl-parse-patternkey :error)
        ,(vl-eof-claim vl-parse-expression-without-failure nil)
        ,(vl-eof-claim vl-parse-scoped-hid nil)
        ,(vl-eof-claim vl-parse-expression :error)
        :hints(;; baseline: 3.58 seconds
               (and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))
               ;; new: 3.59 seconds
               ;; (and acl2::stable-under-simplificationp
               ;;      (expand-only-the-flag-function-hint clause state))
               )))))



(defun vl-expression-claim-fn (name args type)
  `'(,name (implies (force (not (mv-nth 0 (,name . ,args))))
                    (,(case type
                       (:expr 'vl-expr-p)
                       (:exprlist 'vl-exprlist-p)
                       (:atts 'vl-atts-p)
                       (:erange 'vl-erange-p)
                       (:mixed 'vl-mixed-binop-list-p)
                       (:patternkey 'vl-patternkey-p)
                       (:maybe-expr 'vl-maybe-expr-p)
                       (:scopeexpr 'vl-scopeexpr-p)
                       (:evatomlist 'vl-evatomlist-p)
                       (:valuerange 'vl-valuerange-p)
                       (:valuerangelist 'vl-valuerangelist-p)
                       (:assignpat      'vl-assignpat-p)
                       (:hidexpr        'vl-hidexpr-p)
                       (:slicesize      'vl-slicesize-p)
                       (:type           'vl-datatype-p)
                       (:streamexpr     'vl-streamexpr-p)
                       (:streamexprlist 'vl-streamexprlist-p)
                       (:keyvallist     'vl-keyvallist-p)
                       (:maybe-exprlist 'vl-maybe-exprlist-p)
                       (:call-namedargs 'vl-call-namedargs-p)
                       (:call-namedarg-pair '(lambda (x) (and (consp x)
                                                              (stringp (car x))
                                                              (vl-maybe-expr-p (cdr x)))))
                       (otherwise
                        (er hard? 'vl-expression-claim-fn
                            "Bad type: ~x0." type)))
                     (mv-nth 1 (,name . ,args))))))

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
      ,(vl-expression-claim vl-parse-event-expression-2005 :evatomlist)
      ,(vl-expression-claim vl-parse-event-expression-2012 :evatomlist)
      ,(vl-expression-claim vl-parse-event-expression :evatomlist)
      ,(vl-expression-claim vl-parse-clocking-event :evatomlist)
      ,(vl-expression-claim vl-parse-expr-or-clocking-event :expr)
      ,(vl-expression-claim vl-parse-sysfuncall-args :maybe-exprlist)
      ,(vl-expression-claim vl-parse-system-function-call :expr)
      ,(vl-expression-claim vl-parse-mintypmax-expression :expr)
      ,(vl-expression-claim vl-parse-range-expression :erange)
      ,(vl-expression-claim vl-parse-concatenation :expr)
      ,(vl-expression-claim vl-parse-stream-expression :streamexpr)
      ,(vl-expression-claim vl-parse-stream-concatenation :streamexprlist)
      ,(vl-expression-claim vl-parse-1+-stream-expressions-separated-by-commas :streamexprlist)
      ,(vl-expression-claim vl-parse-simple-type :type)
      ,(vl-expression-claim vl-parse-slice-size :slicesize)
      ,(vl-expression-claim vl-parse-any-sort-of-concatenation :expr)
      ,(vl-expression-claim vl-parse-hierarchical-identifier :hidexpr :args (recursivep))
      ,(vl-expression-claim vl-parse-call-namedarg-pair :call-namedarg-pair)
      ,(vl-expression-claim vl-parse-call-namedargs-aux :call-namedargs)
      ,(vl-expression-claim vl-parse-call-namedargs :call-namedargs)
      ,(vl-expression-claim vl-parse-call-plainargs-aux :maybe-exprlist)
      ,(vl-expression-claim vl-parse-call-plainargs :maybe-exprlist)
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
      ,(vl-expression-claim vl-parse-assignment-pattern :assignpat)
      ,(vl-expression-claim vl-parse-1+-keyval-expression-pairs :keyvallist)
      ,(vl-expression-claim vl-parse-open-value-range :valuerange)
      ,(vl-expression-claim vl-parse-1+-open-value-ranges :valuerangelist)
      ,(vl-expression-claim vl-parse-patternkey :patternkey)
      ,(vl-expression-claim vl-parse-expression-without-failure :maybe-expr)
      ,(vl-expression-claim vl-parse-scoped-hid :scopeexpr)
      ,(vl-expression-claim vl-parse-expression :expr)
      :hints(("Goal" :do-not '(generalize fertilize))
             ;; Baseline: 7.49 seconds
             (and stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))
             ;; New: 7.72 seconds
             ;; (and acl2::stable-under-simplificationp
             ;;      (expand-only-the-flag-function-hint clause state))
             )))))

(local (defthm true-listp-when-vl-atts-p-rw
         (implies (vl-atts-p x)
                  (true-listp x))))

;; (local (in-theory (enable vl-arity-ok-p)))

;; (local (defthm l1
;;          (implies
;;           (VL-LOOKAHEAD-IS-TOKEN? :VL-SCOPE (CDR (VL-TOKSTREAM->TOKENS :TOKSTREAM (LIST TOKSTREAM1 TOKSTREAM3))))
;;           (CONSP
;;            (VL-TOKSTREAM->TOKENS
;;             :TOKSTREAM (MV-NTH 2
;;                                (VL-MATCH :TOKSTREAM (LIST TOKSTREAM1 TOKSTREAM3))))))
;;          :hints(("Goal" :in-theory (enable vl-lookahead-is-token?
;;                                            vl-match)))))

(local (defthm vl-maybe-exprlist-p-when-vl-exprlist-p
         (implies (vl-exprlist-p x)
                  (vl-maybe-exprlist-p x))
         :hints(("Goal" :induct (len x))))) 

(with-output
  :off (prove event) :gag-mode :goals
  (verify-guards vl-parse-expression-fn
   ;; :hints ((and stable-under-simplificationp
   ;;              '(:in-theory (enable vl-type-of-matched-token))))
    ;; :guard-debug t
   ))

(defparser-top vl-parse-expression :resulttype vl-expr-p)





; Dimensions and ranges are introduced with the following rules.
;
; dimension ::= '[' dimension_constant_expression ':' dimension_constant_expression ']'
;
; range ::= '[' msb_constant_expression ':' lsb_constant_expression ']'
;
; But these are all just aliases to constant_expression, which we treat as
; regular expressions.  Note also that the names above in "range" are
; misleading, since no particular order is required.  Moreover, we do not make
; any distinction between dimensions and ranges.  That is, in either case, we
; call vl-parse-range and produce vl-range-p objects.

(defparser vl-parse-range ()
  :result (vl-range-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-lbrack))
       (msb := (vl-parse-expression))
       (:= (vl-match-token :vl-colon))
       (lsb := (vl-parse-expression))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-range :msb msb
                              :lsb lsb))))

(defparser vl-parse-0+-ranges ()
  ;; Note: assumes brackets denote subsequent ranges to be matched, and as a
  ;; result it may indeed cause an error.
  :result (vl-rangelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (unless (vl-plausible-start-of-range-p)
         (return nil))
       (first := (vl-parse-range))
       (rest := (vl-parse-0+-ranges))
       (return (cons first rest))))








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


