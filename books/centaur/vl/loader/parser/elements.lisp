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
(include-book "statements")
(include-book "ports")      ;; vl-portdecllist-p, vl-portlist-p
(include-book "nets")       ;; vl-assignlist-p, vl-netdecllist-p
(include-book "blockitems") ;; vl-vardecllist-p, vl-paramdecllist-p, typedefs
(include-book "insts")      ;; vl-modinstlist-p
(include-book "gates")      ;; vl-gateinstlist-p
(include-book "functions")  ;; vl-fundecllist-p
(include-book "modports")
(include-book "imports")
(include-book "asserts")
(include-book "dpi")
(include-book "clocking")
(include-book "classes")
(include-book "covergroups")
(include-book "../../mlib/port-tools")  ;; vl-ports-from-portdecls
(local (include-book "../../util/arithmetic"))




(defparser vl-parse-1+-alias-rhses (atts lhs loc)
  ;; Match '=' net_lvalue { '=' net_lvalue }
  :guard (and (vl-atts-p atts)
              (vl-expr-p lhs)
              (vl-location-p loc))
  :result (vl-aliaslist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-equalsign))
        (rhs1 := (vl-parse-net-lvalue))
        (when (vl-is-token? :vl-equalsign)
          (rest := (vl-parse-1+-alias-rhses atts lhs loc)))
        (return (cons (make-vl-alias :lhs lhs
                                     :rhs rhs1
                                     :atts atts
                                     :loc loc)
                      rest))))

(defparser vl-parse-alias (atts)
  ;; net_alias ::= 'alias' net_lvalue '=' net_lvalue { '=' net_lvalue } ';'
  :guard (vl-atts-p atts)
  :result (vl-aliaslist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (loc := (vl-current-loc))
        (:= (vl-match-token :vl-kwd-alias))
        (lhs := (vl-parse-net-lvalue))
        (aliases := (vl-parse-1+-alias-rhses atts lhs loc))
        (:= (vl-match-token :vl-semi))
        (return aliases)))




(defparser vl-parse-initial-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-initiallist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-token :vl-kwd-initial))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-initial :loc (vl-token->loc kwd)
                                       :stmt stmt
                                       :atts atts)))))

(defparser vl-parse-final-construct (atts)
  ;; SystemVerilog-2012 rules:
  ;;   final_construct ::= 'final' function_statement
  ;;   function_statement ::= statement
  :guard (vl-atts-p atts)
  :result (vl-finallist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-token :vl-kwd-final))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-final :loc (vl-token->loc kwd)
                                     :stmt stmt
                                     :atts atts)))))

(defparser vl-parse-alwaystype ()
  :result (vl-alwaystype-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          (:= (vl-match-token :vl-kwd-always))
          (return :vl-always))
        (kwd := (vl-match-some-token '(:vl-kwd-always
                                       :vl-kwd-always_comb
                                       :vl-kwd-always_latch
                                       :vl-kwd-always_ff)))
        (return (case (vl-token->type kwd)
                  (:vl-kwd-always       :vl-always)
                  (:vl-kwd-always_comb  :vl-always-comb)
                  (:vl-kwd-always_latch :vl-always-latch)
                  (:vl-kwd-always_ff    :vl-always-ff)))))

(defparser vl-parse-always-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-alwayslist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (loc  := (vl-current-loc))
        (type := (vl-parse-alwaystype))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-always :loc  loc
                                      :type type
                                      :stmt stmt
                                      :atts atts)))))




;                           UNIMPLEMENTED PRODUCTIONS
;
; Eventually we may implement some more of these.  For now, we just cause
; an error if any of them is used.
;
; BOZO consider changing some of these to skip tokens until 'endfoo' and issue
; a warning.
;

(defparser vl-parse-specify-block-aux ()
  ;; BOZO this is really not implemented.  We just read until endspecify,
  ;; throwing away any tokens we encounter until it.
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-token? :vl-kwd-endspecify)
          (:= (vl-match))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-specify-block-aux))
        (return nil)))

(defparser vl-parse-specify-block ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (if (not (consp (vl-tokstream->tokens)))
      (vl-parse-error "Unexpected EOF.")
    (seq tokstream
         (:= (vl-parse-warning :vl-warn-specify
                               "Specify blocks are not yet implemented.  Ignoring everything until 'endspecify'."))
         (ret := (vl-parse-specify-block-aux))
         (return ret))))


(defparser vl-parse-specparam-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(define vl-idtokenlist->genvars ((x vl-idtoken-list-p)
                                 (atts vl-atts-p))
  :returns (genvars (and (vl-genvarlist-p genvars)
                         (true-listp genvars)))
  (if (atom x)
      nil
    (cons (make-vl-genvar :name (vl-idtoken->name (car x))
                          :atts atts
                          :loc (vl-token->loc (car x)))
          (vl-idtokenlist->genvars (cdr x) atts))))

(defparser vl-parse-genvar-declaration (atts)
  :parents (parser)
  :short "Match genvar_declaration."
  :long "<p>Verilog-2005 and SystemVerilog-2012 agree on the following
rules:</p>

@({
    genvar_declaration ::= 'genvar' list_of_genvar_identifiers ';'
    list_of_genvar_identifiers ::= genvar_identifier { ',' genvar_identifier }
    genvar_identifier ::= identifier
})"
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-genvar))
       (names := (vl-parse-1+-identifiers-separated-by-commas))
       (:= (vl-match-token :vl-semi))
       (return (vl-idtokenlist->genvars names atts))))


(defparser vl-parse-parameter-override (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(define vl-elaborate-system-task-function-p ((x vl-sysidtoken-p))
  (if (member-equal (vl-sysidtoken->name x)
                    '("$fatal" "$error" "$warning" "$info"))
      t
    nil))

(defparser vl-parse-elaborate-system-task ()
  :guard (and (vl-is-token? :vl-sysidtoken)
              (vl-elaborate-system-task-function-p (car (vl-tokstream->tokens))))
  :result (vl-elabtask-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (enable vl-is-token?))))
  ;; SystemVerilog-2012:
  ;;
  ;; elaboration_system_task ::=
  ;;      '$fatal'   [ '(' finish_number [ ',' list_of_arguments ] ')' ] ';'
  ;;    | '$error'   [ '(' [ list_of_arguments ] ')' ]                   ';'
  ;;    | '$warning' [ '(' [ list_of_arguments ] ')' ]                   ';'
  ;;    | '$info'    [ '(' [ list_of_arguments ] ')' ]                   ';'
  ;;
  ;; finish_number ::= '0' | '1' | '2'
  ;;
  ;; It seems pretty reasonable to be generous with the arguments here
  ;; and just try to handle any system-tf-call of these four functions.
  (seq tokstream
       (stmt := (vl-parse-system-tf-call))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-elabtask :stmt stmt))))


(defconst *vl-netdecltypes-kwds*
  (strip-cars *vl-netdecltypes-kwd-alist*))


(defthm vl-modelement-p-of-vl-parse-fwd-typedef
  (implies (and (force (vl-atts-p atts))
                (force (vl-is-token? :vl-kwd-typedef)))
           (b* (((mv err res) (vl-parse-fwd-typedef atts)))
             (equal (vl-modelement-p res)
                    (not err))))
  :hints(("Goal" :in-theory (enable vl-parse-fwd-typedef))))

(defthm vl-modelement-p-of-vl-parse-type-declaration
  (implies (and (force (vl-atts-p atts))
                (force (vl-is-token? :vl-kwd-typedef)))
           (b* (((mv err res) (vl-parse-type-declaration atts)))
             (equal (vl-modelement-p res)
                    (not err))))
  :hints(("Goal" :in-theory (enable vl-parse-type-declaration))))

(encapsulate nil
  (local (in-theory (enable vl-is-token?)))
  (local (in-theory (disable MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                             VL-PARSE-EXPRESSION-EOF-VL-PARSE-0+-ATTRIBUTE-INSTANCES
                             double-containment
                             acl2::subsetp-when-atom-left
                             acl2::subsetp-when-atom-right
                             acl2::lower-bound-of-len-when-sublistp
                             acl2::len-when-prefixp
                             acl2::len-when-atom
                             default-car)))

  (local (defthm vl-modelement-p-when-vl-blockitem-p
           (implies (vl-blockitem-p x)
                    (vl-modelement-p x))
           :hints(("Goal" :in-theory (enable vl-blockitem-p vl-modelement-p)))))

  (local (defthm vl-modelementlist-p-when-vl-blockitemlist-p
           (implies (vl-blockitemlist-p x)
                    (vl-modelementlist-p x))
           :hints(("Goal" :induct (len x)))))

  (defparser vl-parse-modelement-aux (atts)
    :guard (vl-atts-p atts)
    :result (vl-modelementlist-p val)
    :resultp-of-nil t
    :true-listp t
    :fails gracefully
    :count strong
    (b* ((tokens (vl-tokstream->tokens))
         (edition (vl-loadconfig->edition config))
         ((when (atom tokens))
          (vl-parse-error "Unexpected EOF."))
         (type1 (vl-token->type (car tokens)))
         ((when (member-eq type1 *vl-directions-kwds*))
          (seq tokstream
                ((portdecls . netdecls) := (vl-parse-port-declaration-noatts atts))
                (:= (vl-match-token :vl-semi))
                ;; Should be fewer netdecls so this is the better order for the append.
                (return (append netdecls portdecls))))
         ((when (eq type1 :vl-kwd-specify))
          (if atts
              (vl-parse-error "'specify' is not allowed to have attributes.")
            (vl-parse-specify-block)))
         ((when (or (eq type1 :vl-kwd-parameter)
                    (eq type1 :vl-kwd-localparam)))
          (seq tokstream
               ;; BOZO local parameters aren't allowed in some contexts, but we don't currently
               ;; have a good way to prohibit them.
               (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-parameter :vl-kwd-localparam)))
               (:= (vl-match-token :vl-semi))
               (return ret)))
         ((when (eq type1 :vl-kwd-specparam))
          (vl-parse-specparam-declaration atts))
         ((when (member type1 *vl-netdecltypes-kwds*))
          (seq tokstream
                ((assigns . decls) := (vl-parse-net-declaration atts))
                ;; Note: this order is important, the decls have to come first
                ;; or we'll try to infer implicit nets from the assigns.
                (return (append decls assigns))))
         ((when (member type1 *vl-gate-type-keywords*))
          (vl-parse-gate-instantiation atts))
         ((when (eq type1 :vl-kwd-genvar))
          (vl-parse-genvar-declaration atts))
         ((when (eq type1 :vl-kwd-task))
          (vl-parse-task-declaration atts))
         ((when (eq type1 :vl-kwd-function))
          (vl-parse-function-declaration atts))
         ((when (eq type1 :vl-kwd-defparam))
          (vl-parse-parameter-override atts))
         ((when (eq type1 :vl-kwd-assign))
          (vl-parse-continuous-assign atts))
         ((when (eq type1 :vl-kwd-initial))
          (vl-parse-initial-construct atts))
         ((when (eq type1 :vl-kwd-always))
          (vl-parse-always-construct atts))

         ((when (eq edition :verilog-2005))
          (case type1
            (:vl-kwd-reg        (vl-parse-reg-declaration atts))
            (:vl-kwd-integer    (vl-parse-integer-declaration atts))
            (:vl-kwd-real       (vl-parse-real-declaration atts))
            (:vl-kwd-time       (vl-parse-time-declaration atts))
            (:vl-kwd-realtime   (vl-parse-realtime-declaration atts))
            (:vl-kwd-event      (vl-parse-event-declaration atts))
            (:vl-idtoken        (vl-parse-udp-or-module-instantiation atts))
            (t (vl-parse-error "Invalid module or generate item."))))

         ;; SystemVerilog extensions ----
         ((when (eq type1 :vl-kwd-final))
          (vl-parse-final-construct atts))

         ((when (eq type1 :vl-kwd-typedef))
          (seq tokstream
                (typedef := (vl-parse-type-declaration atts))
                (return (list typedef))))

         ((when (eq type1 :vl-kwd-modport))
          (seq tokstream
                (modports := (vl-parse-modport-decl atts))
                (return modports)))

         ((when (eq type1 :vl-kwd-alias))
          (seq tokstream
                (aliases := (vl-parse-alias atts))
                (return aliases)))

         ((when (eq type1 :vl-kwd-import))
          (seq tokstream
               (when (vl-plausible-start-of-package-import-p)
                 (imports := (vl-parse-package-import-declaration atts))
                 (return imports))
               ;; Otherwise maybe it's a DPI import.
               (dpiimport := (vl-parse-dpi-import atts))
               (return (list dpiimport))))

         ((when (eq type1 :vl-kwd-export))
          (seq tokstream
               (dpiexport := (vl-parse-dpi-export atts))
               (return (list dpiexport))))

         ((when (or (eq type1 :vl-kwd-always_ff)
                    (eq type1 :vl-kwd-always_latch)
                    (eq type1 :vl-kwd-always_comb)))
          (vl-parse-always-construct atts))

         ((when (vl-plausible-start-of-assertion-item-p))
          ;; These are for things like actual 'assert property ...' and
          ;; similar, not for property/sequence declarations.
          ;; BOZO -- Darn it, don't have anywhere to put the atts.
          (vl-parse-assertion-item))

         ;; assertion_item_declaration ::= property_declaration
         ;;                              | sequence_declaration
         ;;                              | let_declaration
         ((when (eq type1 :vl-kwd-property))
          ;; BOZO are these supposed to have atts?
          (seq tokstream
               (property := (vl-parse-property-declaration))
               (return (list property))))

         ((when (eq type1 :vl-kwd-sequence))
          ;; BOZO are these supposed to have atts?
          (seq tokstream
               (sequence := (vl-parse-sequence-declaration))
               (return (list sequence))))

         ((when (eq type1 :vl-kwd-global))
          (seq tokstream
               (gclkdecl := (vl-parse-global-clocking-declaration atts))
               (return (list gclkdecl))))

         ((when (or (and (eq type1 :vl-kwd-default)
                         (vl-lookahead-is-token? :vl-kwd-clocking (cdr tokens)))
                    (eq type1 :vl-kwd-clocking)))
          (seq tokstream
               (clkdecl := (vl-parse-normal-clocking-declaration atts))
               (return (list clkdecl))))

         ((when (eq type1 :vl-kwd-default))
          ;; Note that we already checked for 'default clocking' above
          (seq tokstream
               (disable := (vl-parse-defaultdisable atts))
               (return (list disable))))

         ((when (eq type1 :vl-kwd-let))
          (vl-parse-error "BOZO not yet implemented: let declarations"))

         ((when (eq type1 :vl-kwd-bind))
          (seq tokstream
               (bind := (vl-parse-bind-directive atts))
               (return (list bind))))

         ((when (or (eq type1 :vl-kwd-class)
                    (eq type1 :vl-kwd-virtual)))
          (seq tokstream
               (class := (vl-parse-class-declaration atts))
               (return (list class))))

         ((when (eq type1 :vl-kwd-covergroup))
          (seq tokstream
               (covergroup := (vl-parse-covergroup-declaration atts))
               (return (list covergroup))))

         ((when (eq type1 :vl-semi))
          ;; SystemVerilog-2012 seems to allow allows empty items to occur most anywhere:
          ;;
          ;;    package_or_generate_item_declaration ::= .... | ';'
          ;;
          ;; And these are allowed all over, e.g., in module_or_generate_item,
          ;; interface_or_generate_item.  We'll match these but just throw them
          ;; away.  This maybe isn't quite right, as it throws away the attributes
          ;; that are associated with the semicolon, but it seems unlikely that
          ;; we will care about that.
          (seq tokstream
               (:= (vl-match))
               (return nil)))

         ((when (and (eq type1 :vl-sysidtoken)
                     (vl-elaborate-system-task-function-p (car tokens))))
          (seq tokstream
               (task := (vl-parse-elaborate-system-task))
               (return (list task))))

         ((when (eq type1 :vl-idtoken))
          ;; It's either a udp/module/interface instance, a variable decl, or a
          ;; (non-ansi) interface port decl.  We'll backtrack to distinguish
          ;; the first two, but we'll parse the interface portdecl as a vardecl
          ;; and fix it up in annotate.
          (b* ((backup (vl-tokstream-save))
               ((mv err1 inst tokstream)
                (vl-parse-udp-or-module-instantiation atts))
               ((unless err1) (mv nil inst tokstream))
               (pos1 (vl-tokstream->position))
               (tokstream (vl-tokstream-restore backup))
               ((mv err2 vardecl tokstream)
                (vl-parse-block-item-declaration-noatts atts))
               ((unless err2) (mv nil vardecl tokstream))
               (pos2 (vl-tokstream->position))
               ((mv pos err) (vl-choose-parse-error pos1 err1 pos2 err2))
               (tokstream (vl-tokstream-restore backup))
               (tokstream (vl-tokstream-update-position pos)))
            (mv err nil tokstream))))


      ;; SystemVerilog -- BOZO haven't thought this through very thoroughly, but it's
      ;; probably a fine starting place.
      (vl-parse-block-item-declaration-noatts atts))))

(defparser vl-parse-modelement ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (return-raw
         (vl-parse-modelement-aux atts))))





(encapsulate nil
  (local (in-theory (disable acl2::len-when-atom
                             acl2::len-when-prefixp
                             acl2::lower-bound-of-len-when-sublistp
                             not)))
  (defparser vl-parse-genloop-header ()
    ;; Parses the "for (init; continue; incr)" header of a generate loop.
    ;; Returns a genloop structure but with an empty body.
    :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-for))
    :result (and (vl-genelement-p val)
                 (equal (vl-genelement-kind val) :vl-genloop))
    :fails gracefully
    :count strong

    ;; loop_generate_construct ::=
    ;;   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
    ;;      generate_block
    ;; genvar_initialization ::=
    ;;    [ genvar ] genvar_identifier = constant_expression
    ;; genvar_iteration ::=
    ;;    genvar_identifier assignment_operator genvar_expression
    ;;    | inc_or_dec_operator genvar_identifier
    ;;    | genvar_identifier inc_or_dec_operator
    (seq tokstream
         (loc := (vl-current-loc))
         (:= (vl-match))
         (:= (vl-match-token :vl-lparen))
         (genvar := (vl-maybe-match-token :vl-kwd-genvar)) ;; skip genvar
         (id := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-equalsign))
         (init := (vl-parse-expression))
         (:= (vl-match-token :vl-semi))
         (continue := (vl-parse-expression))
         (:= (vl-match-token :vl-semi))
         ((id2 . next) := (vl-parse-operator-assignment/inc/dec))
         (when (not (and (vl-idexpr-p id2)
                         (equal (vl-idtoken->name id)
                                (vl-idexpr->name id2))))
           (return-raw
            (vl-parse-error "For loop: the initialized variable differed from the incremented variable.")))
         (:= (vl-match-token :vl-rparen))
         (return (make-vl-genloop :var (vl-idtoken->name id)
                                  :genvarp (and genvar t)
                                  :initval init
                                  :continue continue
                                  :nextval next
                                  :body (make-vl-genblock :loc loc)
                                  :loc loc)))))

(encapsulate nil
  (table acl2::acl2-defaults-table :ruler-extenders :all)
  (local (in-theory (disable acl2::len-when-atom
                             acl2::len-when-prefixp
                             acl2::lower-bound-of-len-when-sublistp
                             vl-is-token?-fn-when-atom-of-tokens
                             vl-parse-expression-eof-vl-parse-expression
                             double-containment
                             acl2::consp-of-car-when-alistp)))

  (local (defthm vl-tokentype-p-implies-symbolp
           (implies (vl-tokentype-p x)
                    (symbolp x))
           :hints(("Goal" :in-theory (enable vl-tokentype-p)))
           :rule-classes :compound-recognizer))

  (with-output :off (prove)
    (defparsers vl-genelements
      :parents (parser)
      :short "Parser for elements contained within modules, interfaces, etc., including
              generate constructs."
      :long "
<p>The structure of these is a little confusing -- here is some clarification:</p>
<ul>

<li>@('vl-parse-generate') parses a generate construct if the current token is
one of @('for'), @('if'), @('case'), or @('begin').  If the first token isn't
any of these keywords, it returns NIL.</li>

<li>@('vl-parse-genelement') parses a generate construct or modelement and
returns a list of genelements (because parsing a single modelement may produce
more than one, e.g. in the case of a netdeclaration with implicit
assignment.)</li>

<li>@('vl-parse-generate-block') parses a generate construct or modelement and
returns a @(see vl-genblock).</li>

</ul>"
      :flag-local nil
      (defparser vl-parse-generate ()
        :measure (two-nats-measure (vl-tokstream-measure) 5)
        (seq tokstream
             (when (vl-is-token? :vl-kwd-for)
               (loopblk := (vl-parse-genloop))
               (return loopblk))
             (when (vl-is-token? :vl-kwd-if)
               (ifblk := (vl-parse-genif))
               (return ifblk))
             (when (vl-is-token? :vl-kwd-case)
               (caseblk := (vl-parse-gencase))
               (return caseblk))
             (when (vl-is-token? :vl-kwd-begin)
               (loc := (vl-current-loc))
               (:= (vl-match))
               (when (vl-is-token? :vl-colon)
                 (:= (vl-match))
                 (blkname := (vl-match-token :vl-idtoken)))
               (elts := (vl-parse-genelements-until :vl-kwd-end))
               (:= (vl-match-token :vl-kwd-end))
               (when blkname
                 ;; SystemVerilog-2012 extends generate_block with [ ':'
                 ;; generate_block_identifier ] at the end.  We don't
                 ;; have to check for SystemVerilog-2012 mode since
                 ;; that's baked into vl-parse-endblock-name.
                 (:= (vl-parse-endblock-name (vl-idtoken->name blkname) "begin/end")))
               (return (make-vl-genbegin
                        :block (make-vl-genblock :name (and blkname
                                                            (vl-idtoken->name blkname))
                                                 :elems elts
                                                 :loc loc))))
             (return nil)))

      (defparser vl-parse-genelement ()
        ;; :result (vl-genelementlist-p val)
        ;; :resultp-of-nil t
        ;; :true-listp t
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 6)
        :verify-guards nil
        (declare (xargs :measure-debug t))
        (seq tokstream
             (gen :w= (vl-parse-generate))
             (when gen
               (return (list gen)))
             (items := (vl-parse-modelement))
             (return (vl-modelementlist->genelements items))))

      (defparser vl-parse-generate-block (directly-under-condp)
        :measure (two-nats-measure (vl-tokstream-measure) 6)
        :verify-guards nil
        (declare (xargs :measure-debug t))
        ;; SystemVerilog-2012:
        ;;
        ;;    generate_block ::= generate_item
        ;;                     | [ identifier ':' ] begin [ ':' identifier ]
        ;;                          {generate_item}
        ;;                       'end' [ ':' identifier ]
        ;;
        ;; BOZO we don't currently support pre-labels.
        (seq tokstream
             (loc := (vl-current-loc))
             (gen :w= (vl-parse-generate))
             (when gen
               (return
                ;; If what we parsed is already a block, just return that,
                ;; otherwise wrap it as a singleton element in a block.
                (if directly-under-condp
                    (vl-genelement-case gen
                      :vl-genbegin gen.block
                      :vl-genif (make-vl-genblock :loc loc
                                                   :elems (list gen)
                                                   :condnestp t)
                      :vl-gencase (make-vl-genblock :loc loc
                                                    :elems (list gen)
                                                    :condnestp t)
                      :otherwise (make-vl-genblock :loc loc
                                                   :elems (list gen)))
                  (vl-genelement-case gen
                    :vl-genbegin gen.block
                    :otherwise (make-vl-genblock :loc loc
                                                 :elems (list gen))))))
             (items := (vl-parse-modelement))
             (return (make-vl-genblock :loc loc
                                       :elems (vl-modelementlist->genelements items)))))

      (defparser vl-parse-genelements-until (endkwd)
        :guard (vl-tokentype-p endkwd)
        ;;:result (vl-genelementlist-p val)
        ;; :resultp-of-nil t
        ;; :true-listp t
        ;; :fails never
        ;; :count weak
        :measure (two-nats-measure (vl-tokstream-measure) 8)
        (declare (xargs :ruler-extenders :all))
        (seq tokstream
             (when (vl-is-token? endkwd)
               (return nil))

             (when (vl-is-token? :vl-kwd-generate)
               (:= (vl-match))
               (elems :w= (vl-parse-genelements-until :vl-kwd-endgenerate))
               (:= (vl-match-token :vl-kwd-endgenerate))
               (rest := (vl-parse-genelements-until endkwd))
               (return (append elems rest)))

             (first :s= (vl-parse-genelement))
             (rest := (vl-parse-genelements-until endkwd))
             (return (append first rest))))

      (defparser vl-parse-genloop ()
        :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-for))
        ;; :result (vl-genelement-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 4)

        ;; loop_generate_construct ::=
        ;;   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
        ;;      generate_block
        ;; genvar_initialization ::=
        ;;    [ genvar ] genvar_identifier = constant_expression
        ;; genvar_iteration ::=
        ;;    genvar_identifier assignment_operator genvar_expression
        ;;    | inc_or_dec_operator genvar_identifier
        ;;    | genvar_identifier inc_or_dec_operator
        (seq tokstream
             (header := (vl-parse-genloop-header))
             (body := (vl-parse-generate-block nil))
             (return (change-vl-genloop header
                                        :body body))))

      (defparser vl-parse-genif ()
        :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-if))
        ;; :result (vl-genelement-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 4)
        ;; if_generate_construct ::=
        ;;   if ( constant_expression ) generate_block [ else generate_block ]
        (seq tokstream
             (loc := (vl-current-loc))
             (:= (vl-match))
             (:= (vl-match-token :vl-lparen))
             (test := (vl-parse-expression))
             (:= (vl-match-token :vl-rparen))
             (then :w= (vl-parse-generate-block t))
             (when (and (consp (vl-tokstream->tokens))
                        (vl-is-token? :vl-kwd-else))
               (:= (vl-match))
               (else := (vl-parse-generate-block t)))
             (return (make-vl-genif
                      :test test
                      :then then
                      :else (or else
                                (make-vl-genblock :loc loc))
                      :loc loc))))

      (defparser vl-parse-gencase ()
        :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-case))
        ;; :result (vl-genelement-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 4)
        ;; case_generate_construct ::=
        ;;    case ( constant_expression ) case_generate_item { case_generate_item } endcase
        ;; case_generate_item ::=
        ;;    constant_expression { , constant_expression } : generate_block
        ;;    | default [ : ] generate_block
        (seq tokstream
             (loc := (vl-current-loc))
             (:= (vl-match))
             (:= (vl-match-token :vl-lparen))
             (test := (vl-parse-expression))
             (:= (vl-match-token :vl-rparen))
             ((caselist . default) := (vl-parse-gencaselist))
             (return (make-vl-gencase
                       :test test
                       :cases caselist
                       :default (or default (make-vl-genblock :loc loc))
                       :loc loc))))

      (defparser vl-parse-gencaselist ()
        ;; :result (and (consp val)
        ;;              (vl-gencaselist-p (car val))
        ;;              (iff (vl-generateblock-p (cdr val))
        ;;                   (cdr val)))
        :measure (two-nats-measure (vl-tokstream-measure) 5)
        (seq tokstream
             (when (vl-is-token? :vl-kwd-endcase)
               (:= (vl-match))
               (return (cons nil nil)))
             (when (vl-is-token? :vl-kwd-default)
               (:= (vl-match))
               (:= (vl-match-token :vl-colon))
               (blk :w= (vl-parse-generate-block t))
               ((rest . rdefault) := (vl-parse-gencaselist))
               (when rdefault
                 (return-raw (vl-parse-error "Multiple default cases in generate case")))
               (return (cons rest blk)))
             (exprs := (vl-parse-1+-expressions-separated-by-commas))
             (:= (vl-match-token :vl-colon))
             (blk :w= (vl-parse-generate-block t))
             ((rest . default) := (vl-parse-gencaselist))
             (return (cons (cons (cons exprs blk) rest) default))))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-val-when-error
      ,(vl-val-when-error-claim vl-parse-genelement)
      ,(vl-val-when-error-claim vl-parse-generate)
      ,(vl-val-when-error-claim vl-parse-generate-block :args (directly-under-condp))
      ,(vl-val-when-error-claim vl-parse-genelements-until :args (endkwd))
      ,(vl-val-when-error-claim vl-parse-genloop)
      ,(vl-val-when-error-claim vl-parse-genif)
      ,(vl-val-when-error-claim vl-parse-gencase)
      ,(vl-val-when-error-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-warning
      ,(vl-warning-claim vl-parse-genelement)
      ,(vl-warning-claim vl-parse-generate)
      ,(vl-warning-claim vl-parse-generate-block :args (directly-under-condp))
      ,(vl-warning-claim vl-parse-genelements-until :args (endkwd))
      ,(vl-warning-claim vl-parse-genloop)
      ,(vl-warning-claim vl-parse-genif)
      ,(vl-warning-claim vl-parse-gencase)
      ,(vl-warning-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-progress
      ,(vl-progress-claim vl-parse-genelement)
      (VL-PARSE-GENERATE
       (AND
        (<= (VL-TOKSTREAM-MEASURE :TOKSTREAM (MV-NTH 2 (VL-PARSE-GENERATE)))
            (VL-TOKSTREAM-MEASURE))
        (IMPLIES
         ;; slightly different claim here than usual
         (and (NOT (MV-NTH 0 (VL-PARSE-GENERATE)))
              (mv-nth 1 (vl-parse-generate)))
         (< (VL-TOKSTREAM-MEASURE :TOKSTREAM (MV-NTH 2 (VL-PARSE-GENERATE)))
            (VL-TOKSTREAM-MEASURE))))
       :RULE-CLASSES ((:REWRITE) (:LINEAR)))
      ,(vl-progress-claim vl-parse-generate-block :args (directly-under-condp))
      ,(vl-progress-claim vl-parse-genelements-until :args (endkwd) :strongp nil)
      ,(vl-progress-claim vl-parse-genloop)
      ,(vl-progress-claim vl-parse-genif)
      ,(vl-progress-claim vl-parse-gencase)
      ,(vl-progress-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (local
   (defmacro vl-genelement-claim (name type &key args true-listp)
     (let ((main `(implies (not (mv-nth 0 (,name . ,args)))
                           (,type (mv-nth 1 (,name . ,args))))))
       `'(,name ,(if true-listp
                     `(and (true-listp (mv-nth 1 (,name . ,args)))
                           ,main)
                   main)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-type
      ,(vl-genelement-claim vl-parse-genelement        vl-genelementlist-p)
      ,(vl-genelement-claim vl-parse-generate          (lambda (val)
                                                         (iff (vl-genelement-p val) val)))
      ,(vl-genelement-claim vl-parse-generate-block    vl-genblock-p :args (directly-under-condp))
      ,(vl-genelement-claim vl-parse-genelements-until vl-genelementlist-p :args (endkwd) :true-listp t)
      ,(vl-genelement-claim vl-parse-genloop           vl-genelement-p)
      ,(vl-genelement-claim vl-parse-genif             vl-genelement-p)
      ,(vl-genelement-claim vl-parse-gencase           vl-genelement-p)
      ,(vl-genelement-claim vl-parse-gencaselist       (lambda (val)
                                                         (and (consp val)
                                                              (vl-gencaselist-p (car val))
                                                              (iff (vl-genblock-p (cdr val))
                                                                   (cdr val)))))
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (defthm true-listp-of-vl-parse-genelement
    (true-listp (mv-nth 1 (vl-parse-genelement)))
    :hints (("goal" :expand ((vl-parse-genelement))))
    :rule-classes :type-prescription)

  (verify-guards vl-parse-genelement-fn
    :guard-debug t))



(define vl-modelement->short-kind-string ((x vl-modelement-p))
  :parents (vl-modelement)
  :short "Human-readable description of what kind of module element this is."
  :returns (str stringp :rule-classes :type-prescription)
  (case (tag x)
    ;; Try to make sure these get properly pluralized by tacking on an "s"
    (:vl-portdecl   "port declaration")
    (:vl-assign     "continuous assignment")
    (:vl-alias      "alias declaration")
    (:vl-vardecl    "variable declaration")
    (:vl-paramdecl  "parameter declaration")
    (:vl-fundecl    "function declaration")
    (:vl-taskdecl   "task declaration")
    (:vl-modinst    "module instance")
    (:vl-gateinst   "gate instance")
    (:vl-always     "always statement")
    (:vl-initial    "initial statement")
    (:vl-final      "final statement")
    (:vl-typedef    "typedef")
    (:vl-fwdtypedef "forward typedef")
    (:vl-import     "package import")
    (:vl-modport    "modport declaration")
    (:vl-genvar     "genvar declaration")
    (:vl-assertion  "immediate assertion")
    (:vl-cassertion "concurrent assertion")
    (:vl-property   "property declaration")
    (:vl-sequence   "sequence declaration")
    (:vl-clkdecl    "clocking declaration")
    (:vl-gclkdecl   "global clocking declaration")
    (:vl-defaultdisable "default disable")
    (:vl-dpiimport  "DPI import")
    (:vl-dpiexport  "DPI export")
    (:vl-bind       "bind declaration")
    (:vl-class      "class declaration")
    (:vl-covergroup "covergroup")
    (:vl-elabtask   "elaborate (e.g., $fatal, ...) system task")
    (otherwise      (progn$ (impossible)
                            "invalid"))))

(define vl-genelement->short-kind-string ((x vl-genelement-p))
  :parents (vl-genelement)
  :short "Human-readable description of what kind of module element this is."
  :returns (str stringp :rule-classes :type-prescription)
  (vl-genelement-case x
    :vl-genbase (vl-modelement->short-kind-string x.item)
    ;; Try to make sure these get properly pluralized by tacking on an "s"
    :vl-genloop "generate loop"
    :vl-genif "generate if statement"
    :vl-gencase "generate case statement"
    :vl-genbegin "generate"
    :vl-genarray "generate loop"))

(defines vl-genelement-findbad
  :parents (vl-genelement)
  :short "Find the first occurrence of any @(see vl-genelement) that isn't
among the listed types."
  :long "<p>This is useful for reusing the generic element parsing code in
contexts where some of the items aren't allowed.</p>"

  (define vl-genelement-findbad ((x       vl-genelement-p)
                                 (allowed symbol-listp))
    :measure (vl-genelement-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (b* ((x (vl-genelement-fix x)))
      (vl-genelement-case x
        :vl-genbase (if (member (tag x.item) allowed)
                        nil
                      x)
        :vl-genbegin (if (member :vl-generate allowed)
                         (vl-genblock-findbad x.block allowed)
                       x)
        :vl-genloop (if (member :vl-generate allowed)
                        (vl-genblock-findbad x.body allowed)
                      x)
        :vl-genif   (if (member :vl-generate allowed)
                        (or (vl-genblock-findbad x.then allowed)
                            (vl-genblock-findbad x.else allowed))
                      x)
        :vl-gencase (if (member :vl-generate allowed)
                        (or (vl-gencaselist-findbad x.cases allowed)
                            (vl-genblock-findbad x.default allowed))
                      x)
        :vl-genarray (if (member :vl-generate allowed)
                         (vl-genblocklist-findbad x.blocks allowed)
                       x))))

  (define vl-genblock-findbad ((x       vl-genblock-p)
                               (allowed symbol-listp))
    :measure (vl-genblock-count x)
    :guard   (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (b* (((vl-genblock x)))
      (vl-genelementlist-findbad x.elems allowed)))

  (define vl-genelementlist-findbad ((x vl-genelementlist-p)
                                     (allowed symbol-listp))
    :measure (vl-genelementlist-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (if (atom x)
        nil
      (or (vl-genelement-findbad (car x) allowed)
          (vl-genelementlist-findbad (cdr x) allowed))))

  (define vl-gencaselist-findbad ((x vl-gencaselist-p)
                                  (allowed symbol-listp))
    :measure (vl-gencaselist-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x))
          nil)
         ((cons (cons ?expr block) rest) x))
      (or (vl-genblock-findbad block allowed)
          (vl-gencaselist-findbad rest allowed))))

  (define vl-genblocklist-findbad ((x vl-genblocklist-p)
                                        (allowed symbol-listp))
    :measure (vl-genblocklist-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (if (atom x)
        nil
      (or (vl-genblock-findbad (car x) allowed)
          (vl-genblocklist-findbad (cdr x) allowed)))))

