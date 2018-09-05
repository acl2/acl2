; VL Verilog Toolkit - Clocking Block Parsing
; Copyright (C) 2016 Apple, Inc.
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
; Original author: Jared Davis

(in-package "VL")
(include-book "asserts")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defxdoc parse-clocking
  :parents (parser)
  :short "Functions for parsing SystemVerilog clocking blocks.")

(local (xdoc::set-default-parents parse-clocking))

(defparser vl-parse-clocking-skew ()
  :result (vl-clkskew-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :short "Match @('clocking_skew')."
  :long "<p>SystemVerilog-2012:</p>
         @({
             clocking_skew ::= edge_identifier [delay_control]
                             | delay_control
         })"
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-posedge :vl-kwd-negedge :vl-kwd-edge))
         (edge := (vl-match)))
       (when (vl-is-token? :vl-pound)
         (delay := (vl-parse-delay-control)))
       (unless (or edge delay)
         (return-raw (vl-parse-error "Expected edge identifier or #delay.")))
       (return
        (make-vl-clkskew
         :delay (and delay (vl-delaycontrol->value delay))
         :edge  (case (and edge (vl-token->type edge))
                  (:vl-kwd-posedge :vl-posedge)
                  (:vl-kwd-negedge :vl-negedge)
                  (:vl-kwd-edge    :vl-edge)
                  (otherwise       :vl-noedge)))))
  ///
  (defthm vl-parse-clocking-skew-is-also-a-maybe-clkskew
    (b* (((mv ?err val ?tokstream) (vl-parse-clocking-skew)))
      (vl-maybe-clkskew-p val))))

(defparser vl-maybe-parse-clocking-skew ()
  :result (vl-maybe-clkskew-p val)
  :resultp-of-nil t
  :fails gracefully
  :count weak
  :short "Match @('[clocking_skew]')."
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-posedge :vl-kwd-negedge :vl-kwd-edge :vl-pound))
         (skew := (vl-parse-clocking-skew))
         (return skew))
       ;; Otherwise doesn't look like a clock skew so don't return anything
       (return nil)))

(defprod vl-clocking-direction-head
  :short "Temporary structure for parsing."
  :tag :vl-clocking-direction-head
  :layout :tree
  ((inp   booleanp)
   (outp  booleanp)
   (iskew vl-maybe-clkskew-p)
   (oskew vl-maybe-clkskew-p)))

(defparser vl-parse-clocking-direction ()
  :result (vl-clocking-direction-head-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :short "Matches @('clocking_direction')."
  :long "<p>SystemVerilog Grammar:</p>
         @({
             clocking_direction ::=
                'input'  [ clocking_skew ]
              | 'output' [ clocking_skew ]
              | 'input' [ clocking_skew ] 'output' [ clocking_skew ]
              | 'inout'
         })"
  (seq tokstream
       (when (vl-is-token? :vl-kwd-inout)
         ;; inout takes no skews, corresponds to an input and output
         (:= (vl-match))
         (return (make-vl-clocking-direction-head :inp t
                                                  :outp t
                                                  :iskew nil
                                                  :oskew nil)))

       (when (vl-is-token? :vl-kwd-output)
         (:= (vl-match))
         (oskew := (vl-maybe-parse-clocking-skew))
         (return (make-vl-clocking-direction-head :inp nil
                                                  :outp t
                                                  :iskew nil
                                                  :oskew oskew)))

       (:= (vl-match-token :vl-kwd-input))
       (iskew := (vl-maybe-parse-clocking-skew))
       (when (vl-is-token? :vl-kwd-output)
         (output := (vl-match))
         (oskew  := (vl-maybe-parse-clocking-skew)))
       (return (make-vl-clocking-direction-head :inp t
                                                :outp (if output t nil)
                                                :iskew iskew
                                                :oskew oskew))))

(defparser vl-parse-list-of-clocking-decl-assigns (head)
  :guard (vl-clocking-direction-head-p head)
  :result (vl-clkassignlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :short "Match @('list_of_clocking_decl_assign')."
  :long "<p>SystemVerilog-2012 grammar:</p>
         @({
             clocking_decl_assign ::= identifier [ '=' expression ]
             list_of_clocking_decl_assign ::= clocking_decl_assign { ',' clocking_decl_assign }
         })"
  (b* (((vl-clocking-direction-head head)))
    (seq tokstream
         (id := (vl-match-token :vl-idtoken))
         (when (vl-is-token? :vl-equalsign)
           (:= (vl-match))
           (rhs := (vl-parse-expression)))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-list-of-clocking-decl-assigns head)))
         (return
          (b* ((ans rest)
               (ans (if (not head.outp)
                        ans
                      (cons (make-vl-clkassign :name   (vl-idtoken->name id)
                                               :inputp nil
                                               :rhs    rhs
                                               :skew   head.oskew
                                               :loc    (vl-token->loc id))
                            ans)))
               (ans (if (not head.inp)
                        ans
                      (cons (make-vl-clkassign :name   (vl-idtoken->name id)
                                               :inputp t
                                               :rhs    rhs
                                               :skew   head.iskew
                                               :loc    (vl-token->loc id))
                            ans))))
            ans)))))


; Clocking block bodies can have lots of things in them: clocking assignments,
; properties, default clocking statements, etc.  We'll parse these as a mixed
; list of stuff, then sort it out when we create the clocking block.  To do
; that, introduce a mixed type...

(defprod vl-defaultskew-item
  :short "Temporary structure for parsing @('default default_skew') clocking items."
  :tag :vl-defaultskew
  :layout :tree
  ((inputp booleanp :rule-classes :type-prescription)
   (skew   vl-clkskew-p)))

(deftranssum vl-clocking-block-item
  :short "Temporary structure for parsing clocking block bodies."
  (vl-defaultskew-item-p
   vl-clkassign-p
   vl-property-p
   vl-sequence-p))

(fty::deflist vl-clocking-block-item-list
  :elt-type vl-clocking-block-item)

(local (defthm vl-clocking-block-item-list-p-when-vl-clkassignlist-p
         (implies (vl-clkassignlist-p x)
                  (vl-clocking-block-item-list-p x))
         :hints(("Goal" :induct (len x)))))

(defparser vl-parse-default-skew-item ()
  :result (vl-clocking-block-item-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :short "Match @(' 'default' default_skew ';' ')."
  :long "<p>SystemVerilog-2012 Grammar:</p>
         @({
             default_skew ::=
                'input' clocking_skew
              | 'output' clocking_skew
              | 'input' clocking_skew 'output' clocking_skew
         })"
  (seq tokstream
       (:= (vl-match-token :vl-kwd-default))
       ;; Output is simpler so do it first.
       (when (vl-is-token? :vl-kwd-output)
         (:= (vl-match))
         (oskew := (vl-parse-clocking-skew))
         (:= (vl-match-token :vl-semi))
         (return (list (make-vl-defaultskew-item :inputp nil :skew oskew))))

       (:= (vl-match-token :vl-kwd-input))
       (iskew := (vl-parse-clocking-skew))
       (when (vl-is-token? :vl-semi)
         ;; Must just be a lone input skew.
         (:= (vl-match))
         (return (list (make-vl-defaultskew-item :inputp t :skew iskew))))

       ;; No semicolon so it must have an output skew, too.
       (:= (vl-match-token :vl-kwd-output))
       (oskew := (vl-parse-clocking-skew))
       (:= (vl-match-token :vl-semi))
       (return (list (make-vl-defaultskew-item :inputp t   :skew iskew)
                     (make-vl-defaultskew-item :inputp nil :skew oskew)))))

(defparser vl-parse-clocking-block-item ()
  :result (vl-clocking-block-item-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :short "Match a @('clocking_item')."
  :long "<p>SystemVerilog-2012 Grammar:</p>
         @({
             clocking_item ::=
                'default' default_skew ';'
              | clocking_direction list_of_clocking_decl_assign ';'
              | { attribute_instance } assertion_item_declaration
         })"
  (cond ((vl-is-token? :vl-kwd-default)
         (vl-parse-default-skew-item))

        ((vl-is-some-token? '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout))
         (seq tokstream
              (head := (vl-parse-clocking-direction))
              (items := (vl-parse-list-of-clocking-decl-assigns head))
              (:= (vl-match-token :vl-semi))
              (return items)))

        (t
         (seq tokstream
              (atts := (vl-parse-0+-attribute-instances))
              ;; assertion_item_declaration ::= property_declaration
              ;;                              | sequence_declaration
              ;;                              | let_declaration
              (when (vl-is-token? :vl-kwd-property)
                ;; BOZO are these supposed to have atts?
                (property := (vl-parse-property-declaration))
                (return
                 (let ((stupid-hack-to-use-atts atts))
                   (declare (ignore stupid-hack-to-use-atts))
                   (list property))))

              (when (vl-is-token? :vl-kwd-sequence)
                ;; BOZO are these supposed to have atts?
                (sequence := (vl-parse-sequence-declaration))
                (return (list sequence)))

              (when (vl-is-token? :vl-kwd-let)
                (return-raw
                 (vl-parse-error "BOZO not yet implemented: let declarations")))

              (return-raw
               (vl-parse-error "Expected default, clocking assignment, or assertion item"))))))

(defparser vl-parse-clocking-block-items-until-endclocking ()
  :result (vl-clocking-block-item-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (when (vl-is-token? :vl-kwd-endclocking)
         (return nil))
       (first := (vl-parse-clocking-block-item))
       (rest := (vl-parse-clocking-block-items-until-endclocking))
       (return (append first rest))))

(fty::deflist vl-defaultskew-item-list
  :elt-type vl-defaultskew-item)

(define vl-sort-clocking-block-items ((x vl-clocking-block-item-list-p)
                                      (idefaults vl-defaultskew-item-list-p)
                                      (odefaults vl-defaultskew-item-list-p)
                                      (clkassigns vl-clkassignlist-p)
                                      (properties vl-propertylist-p)
                                      (sequences vl-sequencelist-p))
  :returns (mv (idefaults vl-defaultskew-item-list-p)
               (odefaults vl-defaultskew-item-list-p)
               (clkassigns vl-clkassignlist-p)
               (properties vl-propertylist-p)
               (sequences vl-sequencelist-p))
  (if (atom x)
      (mv (vl-defaultskew-item-list-fix idefaults)
          (vl-defaultskew-item-list-fix odefaults)
          (vl-clkassignlist-fix clkassigns)
          (vl-propertylist-fix properties)
          (vl-sequencelist-fix sequences))
    (let* ((item (car x))
           (tag  (tag item)))
      (vl-sort-clocking-block-items
       (cdr x)
       (if (and (eq tag :vl-defaultskew) (vl-defaultskew-item->inputp item))
           (cons item idefaults)
         idefaults)
       (if (and (eq tag :vl-defaultskew) (not (vl-defaultskew-item->inputp item)))
           (cons item odefaults)
         odefaults)
       (if (eq tag :vl-clkassign) (cons item clkassigns) clkassigns)
       (if (eq tag :vl-property) (cons item properties) properties)
       (if (eq tag :vl-sequence) (cons item sequences) sequences)))))

(defparser vl-parse-normal-clocking-declaration (atts)
  :result (vl-clkdecl-p val)
  :guard (vl-atts-p atts)
  :resultp-of-nil nil
  :fails :gracefully
  :count strong
  :guard-debug t
  :short "Match a single, non-global @('clocking_declaration')."
  :long "<p>SystemVerilog-2012 Grammar:</p>
         @({
              clocking_declaration ::=
                 ['default'] 'clocking' [ identifier ] clocking_event ';'
                   {clocking_item}
              'endclocking' [ ':' identifier ]
         })"
  (seq tokstream
       (when (vl-is-token? :vl-kwd-default)
         (default := (vl-match)))
       (kwd := (vl-match-token :vl-kwd-clocking))
       (when (vl-is-token? :vl-idtoken)
         (name := (vl-match)))
       (event := (vl-parse-clocking-event))
       (:= (vl-match-token :vl-semi))
       (unless (or name default)
         ;; Required by SystemVerilog-2012 14.3
         (return-raw (vl-parse-error "Only default clocking blocks may be unnamed.")))
       (items := (vl-parse-clocking-block-items-until-endclocking))
       (:= (vl-match-token :vl-kwd-endclocking))
       (when name
         (:= (vl-parse-endblock-name (and name (vl-idtoken->name name)) "clocking")))
       (return-raw
        (b* (((mv idefaults odefaults clkassigns properties sequences)
              (vl-sort-clocking-block-items items nil nil nil nil nil))
             ((unless (or (atom idefaults) (atom (cdr idefaults))))
              (vl-parse-error "Multiple default input clock skews"))
             ((unless (or (atom odefaults) (atom (cdr odefaults))))
              (vl-parse-error "Multiple default output clock skews"))
             (ans (make-vl-clkdecl
                   :defaultp (if default t nil)
                   :name  (and name
                               (vl-idtoken->name name))
                   :event event
                   :iskew (and (consp idefaults)
                               (vl-defaultskew-item->skew (car idefaults)))
                   :oskew (and (consp odefaults)
                               (vl-defaultskew-item->skew (car odefaults)))
                   :clkassigns clkassigns
                   :properties properties
                   :sequences sequences
                   :loc (vl-token->loc kwd)
                   :atts atts)))
          (mv nil ans tokstream)))))

(defparser vl-parse-global-clocking-declaration (atts)
  :result (vl-gclkdecl-p val)
  :guard (vl-atts-p atts)
  :resultp-of-nil nil
  :fails :gracefully
  :count strong
  :short "Match a single global clocking declaration."
  :long "<p>SystemVerilog-2012 Grammar:</p>
         @({
              clocking_declaration ::= ...
                  | 'global' 'clocking' [identifier] clocking_event ';'
                    'endclocking' [ ':' identifier ]
         })"
  (seq tokstream
       (:= (vl-match-token :vl-kwd-global))
       (clk := (vl-match-token :vl-kwd-clocking))
       (when (vl-is-token? :vl-idtoken)
         (name := (vl-match)))
       (event := (vl-parse-clocking-event))
       (:= (vl-match-token :vl-kwd-endclocking))
       (when name
         (:= (vl-parse-endblock-name (and name (vl-idtoken->name name)) "clocking")))
       (return (make-vl-gclkdecl :name (and name (vl-idtoken->name name))
                                 :event event
                                 :loc (vl-token->loc clk)
                                 :atts atts))))

(defparser vl-parse-defaultdisable (atts)
  :result (vl-defaultdisable-p val)
  :guard (vl-atts-p atts)
  :resultp-of-nil nil
  :fails :gracefully
  :count strong
  :short "Match a single @('default disable iff ...') construct"
  :long "<p>SystemVerilog-2012 Grammar:</p>
         @({
              module_or_generate_item_declaration ::= ...
                  | 'default' 'disable' 'iff' expression_or_dist ';'
         })"
  (seq tokstream
       (disable := (vl-match-token :vl-kwd-default))
       (:= (vl-match-token :vl-kwd-disable))
       (:= (vl-match-token :vl-kwd-iff))
       (exprdist := (vl-parse-expression-or-dist))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-defaultdisable :exprdist exprdist
                                       :loc      (vl-token->loc disable)
                                       :atts     atts))))
