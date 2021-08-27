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
(include-book "elements")
(include-book "classes")
(local (include-book "../../util/arithmetic"))

(defxdoc parse-packages
  :parents (parser)
  :short "Functions for parsing SystemVerilog packages.")

(local (xdoc::set-default-parents parse-packages))

;; package_item ::=
;; package_or_generate_item_declaration
;; | anonymous_program
;; | package_export_declaration
;; | timeunits_declaration

;; package_or_generate_item_declaration ::=
;; net_declaration
;; | data_declaration
;; | task_declaration
;; | function_declaration
;; | checker_declaration
;; | dpi_import_export
;; | extern_constraint_declaration
;; | class_declaration
;; | class_constructor_declaration
;; | local_parameter_declaration ;
;; | parameter_declaration ;
;; | covergroup_declaration
;; | overload_declaration
;; | assertion_item_declaration
;; | ;

;; anonymous_program ::= program ; { anonymous_program_item } endprogram

;; anonymous_program_item ::=
;; task_declaration
;; | function_declaration
;; | class_declaration
;; | covergroup_declaration
;; | class_constructor_declaration
;; | ;

;; anonymous_program_item ::=
;; task_declaration
;; | function_declaration
;; | class_declaration
;; | covergroup_declaration
;; | class_constructor_declaration
;; | ;

(defparser vl-skip-through-endpackage (pkgname)
  :short "Special error recovery for parse errors encountered during packages."
  :guard (stringp pkgname)
  :result (vl-token-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (unless (vl-is-token? :vl-kwd-endpackage)
          (:s= (vl-match-any))
          (endkwd := (vl-skip-through-endpackage pkgname))
          (return endkwd))
        (endkwd := (vl-match))
        (:= (vl-parse-endblock-name pkgname "package/endpackage"))
        (return endkwd)))

(define vl-make-package-with-parse-error ((name   stringp)
                                          (minloc vl-location-p)
                                          (maxloc vl-location-p)
                                          (err    vl-warning-p)
                                          (tokens vl-tokenlist-p))
  :returns (package vl-package-p)
  (b* (;; We also generate a second error message.
       ;;  - This lets us always show the remaining part of the token stream
       ;;    in each case.
       ;;  - It ensures that any module with a parse error always, absolutely,
       ;;    certainly has a fatal warning, even if somehow the real warning
       ;;    isn't marked as fatal.
       (warn2 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens))
                                                  (list-fix tokens)))
                                           (if (> (len tokens) 4) "..." ""))
                               :fatalp t
                               :fn __function__)))
    (make-vl-package :name name
                     :minloc minloc
                     :maxloc maxloc
                     :warnings (list err warn2))))

(defparser vl-parse-genelement-or-class ()
  :result (vl-genelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (gen :w= (vl-parse-generate))
       (when gen
         (return (list gen)))
       (atts := (vl-parse-0+-attribute-instances))
       (when (vl-is-token? :vl-kwd-class)
         (:= (vl-parse-class-declaration atts))
         (return nil))
       (items := (vl-parse-modelement-aux atts))
       (return (vl-modelementlist->genelements items))))


(local (defthm vl-tokentype-p-implies-symbolp
         (implies (vl-tokentype-p x)
                  (symbolp x))
         :hints(("Goal" :in-theory (enable vl-tokentype-p)))
         :rule-classes :compound-recognizer))

(defparser vl-parse-genelements-or-classes-until (endkwd)
  :guard (vl-tokentype-p endkwd)
  :result (vl-genelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  :measure (vl-tokstream-measure)
  (declare (xargs :ruler-extenders :all))
  (seq tokstream
       (when (vl-is-token? endkwd)
         (return nil))

       (when (vl-is-token? :vl-kwd-generate)
         (:= (vl-match))
         (elems :w= (vl-parse-genelements-until :vl-kwd-endgenerate))
         (:= (vl-match-token :vl-kwd-endgenerate))
         (rest := (vl-parse-genelements-or-classes-until endkwd))
         (return (append elems rest)))

       (first :s= (vl-parse-genelement-or-class))
       (rest := (vl-parse-genelements-until endkwd))
       (return (append first rest))))


(defparser vl-parse-package-declaration (atts)
  ;; package_declaration ::= { attribute_instance } package [ lifetime ] package_identifier ;
  ;;                           [ timeunits_declaration ]
  ;;                           { { attribute_instance } package_item }
  ;;                         endpackage [ : package_identifier ]
  :guard (vl-atts-p atts)
  :result (vl-package-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (startkwd := (vl-match-token :vl-kwd-package))
        (lifetime := (vl-maybe-parse-lifetime))
        (name     := (vl-match-token :vl-idtoken))
        (return-raw
         (b* ((backup (vl-tokstream-save))

              ;; Temporarily clear out the warnings so that we can associate any
              ;; warnings encountered while parsing the package with the package
              ;; itself.
              (orig-warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
              (tokstream     (vl-tokstream-update-pstate
                              (change-vl-parsestate (vl-tokstream->pstate) :warnings nil)))

              ;; Now try to parse the rest of the package declaration.
              ((mv err pkg tokstream)
               (seq tokstream
                    (:= (vl-match-token :vl-semi))
                    ;; BOZO parse timeunits declaration stuff.
                    (items  := (vl-parse-genelements-or-classes-until :vl-kwd-endpackage))
                    (endkwd := (vl-match-token :vl-kwd-endpackage))
                    (:= (vl-parse-endblock-name (vl-idtoken->name name) "package/endpackage"))
                    (return
                     (b* ((warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
                          (bad-item (vl-genelementlist-findbad items
                                                               '(;; :vl-generate -- not allowed
                                                                 ;; :vl-port     -- not allowed
                                                                 ;; :vl-portdecl -- not allowed
                                                                 ;; :vl-assign   -- not allowed
                                                                 ;; :vl-alias   -- bozo, let's not permit these yet
                                                                 :vl-vardecl
                                                                 :vl-paramdecl
                                                                 :vl-fundecl
                                                                 :vl-taskdecl
                                                                 ;; :vl-modinst  -- not allowed
                                                                 ;; :vl-gateinst -- not allowed
                                                                 ;; :vl-always   -- not allowed
                                                                 ;; :vl-initial  -- not allowed
                                                                 :vl-typedef
                                                                 :vl-import
                                                                 ;; :vl-fwdtypedef -- not allowed
                                                                 ;; :vl-modport    -- not allowed

                                                                 ;; Don't get confused by assertion_item_declaration;
                                                                 ;; :vl-assertion is not allowed and
                                                                 ;; :vl-cassertion is not allowed either.
                                                                 ;; They are assertion_items, not assertion_item_declarations.
                                                                 :vl-dpiimport
                                                                 :vl-dpiexport
                                                                 :vl-class
                                                                 )))
                          (warnings
                           (if (not bad-item)
                               warnings
                             (fatal :type :vl-bad-package-item
                                    :msg "~a0: a package may not contain a ~s1."
                                    :args (list bad-item (vl-genelement->short-kind-string bad-item)))))

                          ((vl-genblob c) (vl-sort-genelements items)))
                       (make-vl-package :name (vl-idtoken->name name)
                                        :minloc (vl-token->loc startkwd)
                                        :maxloc (vl-token->loc endkwd)
                                        :lifetime lifetime
                                        :vardecls c.vardecls
                                        :paramdecls c.paramdecls
                                        :fundecls c.fundecls
                                        :taskdecls c.taskdecls
                                        :typedefs c.typedefs
                                        :imports c.imports
                                        :classes c.classes
                                        :dpiimports c.dpiimports
                                        :dpiexports c.dpiexports
                                        :warnings warnings
                                        :atts atts
                                        ;; bozo timeunits stuff
                                        ;; bozo package items stuff
                                        )))))

              ((unless err)
               ;; We read the whole thing and made a valid package, so that's great.
               ;; We just need to restore the original warnings and return our answer.
               (let ((tokstream (vl-tokstream-update-pstate
                                 (change-vl-parsestate (vl-tokstream->pstate) :warnings orig-warnings))))
                 (mv nil pkg tokstream)))

              ;; There was some error parsing the package.  Stop everything, go
              ;; back to 'package foo' part.  Scan for a matching 'endpackage'.
              ;; Throw away everything in between and create a fake package
              ;; full of errors.
              (errtokens
               ;; To get the tokens at the point of the error, we need to do this
               ;; before restoring the tokstream!
               (vl-tokstream->tokens))
              (tokstream (vl-tokstream-restore backup)))
           (seq tokstream
                (endkwd := (vl-skip-through-endpackage (vl-idtoken->name name)))
                (return
                 (vl-make-package-with-parse-error (vl-idtoken->name name)
                                                   (vl-token->loc startkwd)
                                                   (vl-token->loc endkwd)
                                                   err
                                                   errtokens)))))))



