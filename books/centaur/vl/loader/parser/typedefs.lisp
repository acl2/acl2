; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "datatypes")
(include-book "../descriptions")
(local (include-book "../../util/arithmetic"))
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not generalize fertilize))

;; type_declaration ::=
;;    'typedef' data_type type_identifier { variable_dimension } ';'
;;  | 'typedef' interface_instance_identifier constant_bit_select '.' type_identifier type_identifier ';'
;;  | 'typedef' [ 'enum' | 'struct' | 'union' | 'class' | 'interface class' ] type_identifier ';'

(defparser vl-parse-fwd-typedef (atts)
  ;; Matches 'typedef' [ 'enum' | 'struct' | 'union' | 'class' | 'interface class' ] type_identifier ';'
  :guard (and (vl-atts-p atts)
              (vl-is-token? :vl-kwd-typedef))
  :result (vl-description-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (typedef := (vl-match))  ;; guard ensures it starts with 'typedef'

        (when (vl-is-token? :vl-kwd-interface)
          (:= (vl-match))
          (:= (vl-match-token :vl-kwd-class))
          (name := (vl-match-token :vl-idtoken))
          (:= (vl-match-token :vl-semi))
          (return (make-vl-fwdtypedef :kind :vl-interfaceclass
                                      :name (vl-idtoken->name name)
                                      :loc (vl-token->loc typedef)
                                      :atts atts)))

        (when (vl-is-some-token? '(:vl-kwd-enum :vl-kwd-struct :vl-kwd-union :vl-kwd-class))
          (type := (vl-match))
          (name := (vl-match-token :vl-idtoken))
          (:= (vl-match-token :vl-semi))
          (return (make-vl-fwdtypedef :kind (case (vl-token->type type)
                                              (:vl-kwd-enum   :vl-enum)
                                              (:vl-kwd-struct :vl-struct)
                                              (:vl-kwd-union  :vl-union)
                                              (:vl-kwd-class  :vl-class))
                                      :name (vl-idtoken->name name)
                                      :loc (vl-token->loc typedef)
                                      :atts atts)))

        (return-raw
         (vl-parse-error "Not a valid forward typedef."))))


(defparser vl-parse-type-declaration (atts)
  :guard (and (vl-atts-p atts)
              (vl-is-token? :vl-kwd-typedef))
  :result (vl-description-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; We use backtracking to figure out if it's a forward or regular type
  ;; declaration.  We try forward declarations first because they're less
  ;; likely to have problems, and we'd probably rather see errors about
  ;; full type declarations.
  (b* (((mv erp fwd fwd-tokens fwd-warnings)
        (vl-parse-fwd-typedef atts))
       ((unless erp)
        ;; Got a valid fwd typedef, so return it.
        (mv erp fwd fwd-tokens fwd-warnings)))

    ;; Else, not a fwd typedef, so try to match a full one.
    (seqw tokens warnings
          (typedef := (vl-match))  ;; guard ensures it starts with 'typedef'

          ;; BOZO the following probably isn't right for the 2nd production.
          (datatype := (vl-parse-datatype))
          (id := (vl-match-token :vl-idtoken))
          (when (vl-is-token? :vl-lbrack)
            (return-raw
             (vl-parse-error "BOZO need to add support for dimensions on typedefs.")))
          (semi := (vl-match-token :vl-semi))
          (return
           (make-vl-typedef :name (vl-idtoken->name id)
                            :type datatype
                            :dims nil ;; BOZO add dimensions
                            :minloc (vl-token->loc typedef)
                            :maxloc (vl-token->loc semi)
                            :atts atts)))))

