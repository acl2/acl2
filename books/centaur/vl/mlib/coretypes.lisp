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
(include-book "../expr")

(defprod vl-coredatatype-info
  :parents (vl-datatype)
  :short "Structure to store properties of a coretype."
  :tag nil
  :layout :tree
  ((coretypename      vl-coretypename-p "name of the coretype")
   (keyword           symbolp :rule-classes :type-prescription
                      "parser keyword for the name")
   (default-signedp   booleanp :rule-classes :type-prescription
                      "what's the default signedness?")
   (takes-signingp    booleanp :rule-classes :type-prescription
                      "does it have an optional [signing] part?")
   (takes-dimensionsp booleanp :rule-classes :type-prescription
                      "does it optionally take dimensions?")
   (4valuedp          booleanp :rule-classes :type-prescription
                      "Is each bit of it 4-valued (as opposed to 2-valued)?")
   (size              maybe-posp :rule-classes :type-prescription
                      "Size, when an integer vector type, nil otherwise")))

(fty::deflist vl-coredatatype-infolist :elt-type vl-coredatatype-info)

(defval *vl-core-data-type-table*
  :parents (vl-datatype)
  :short "Table giving properties of the various Verilog core types."
  (list ;; Note: for default signedness see Table 6-8, "integer data types", page 68.
   ;; -------------------------------------------------------------------------------------------------------------
   ;;                                      parser kwd token    default signed?   [signing]?  dims?  4valued?  size
   ;; -------------------------------------------------------------------------------------------------------------
   ;; special extra core types
   (vl-coredatatype-info   :vl-string      :vl-kwd-string      nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-event       :vl-kwd-event       nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-chandle     :vl-kwd-chandle     nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-void        nil                 nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-untyped     nil                 nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-sequence    nil                 nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-property    nil                 nil               nil         nil    nil       nil  )
   ;; non-integer types                           N/A
   (vl-coredatatype-info   :vl-shortreal   :vl-kwd-shortreal   nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-real        :vl-kwd-real        nil               nil         nil    nil       nil  )
   (vl-coredatatype-info   :vl-realtime    :vl-kwd-realtime    nil               nil         nil    nil       nil  )
   ;; integer atom types
   (vl-coredatatype-info   :vl-byte        :vl-kwd-byte        t                 t           nil    nil       8    )
   (vl-coredatatype-info   :vl-shortint    :vl-kwd-shortint    t                 t           nil    nil       16   )
   (vl-coredatatype-info   :vl-int         :vl-kwd-int         t                 t           nil    nil       32   )
   (vl-coredatatype-info   :vl-longint     :vl-kwd-longint     t                 t           nil    nil       64   )
   (vl-coredatatype-info   :vl-integer     :vl-kwd-integer     t                 t           nil    t         32   )
   (vl-coredatatype-info   :vl-time        :vl-kwd-time        nil               t           nil    t         64   )
   ;; integer vector types
   (vl-coredatatype-info   :vl-bit         :vl-kwd-bit         nil               t           t      nil       1    )
   (vl-coredatatype-info   :vl-logic       :vl-kwd-logic       nil               t           t      t         1    )
   (vl-coredatatype-info   :vl-reg         :vl-kwd-reg         nil               t           t      t         1    )))

(define vl-coredatatype-infolist-find-type ((x vl-coretypename-p)
                                            (table vl-coredatatype-infolist-p))
  :returns (info (iff (vl-coredatatype-info-p info) info))
  (if (atom table)
      nil
    (if (eq (vl-coretypename-fix x) (vl-coredatatype-info->coretypename (car table)))
        (vl-coredatatype-info-fix (car table))
      (vl-coredatatype-infolist-find-type x (cdr table)))))

(define vl-coredatatype-infolist-find-kwd ((x keywordp)
                                           (table vl-coredatatype-infolist-p))
  :returns (info (iff (vl-coredatatype-info-p info) info))
  (if (atom table)
      nil
    (if (eq x (vl-coredatatype-info->keyword (car table)))
        (vl-coredatatype-info-fix (car table))
      (vl-coredatatype-infolist-find-kwd x (cdr table)))))

(define vl-coretypename->info ((x vl-coretypename-p))
  :parents (vl-datatype)
  :short "Find the properties (@(see vl-coredatatype-info) structure) for a coretype."
  :returns (info vl-coredatatype-info-p
                 :hints(("Goal" :in-theory (enable vl-coredatatype-infolist-find-type
                                                   vl-coretypename-p vl-coretypename-fix)
                         :cases ((vl-coretypename-p x)))))
  (vl-coredatatype-infolist-find-type (vl-coretypename-fix x) *vl-core-data-type-table*))
