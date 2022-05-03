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
(include-book "../util/fmt-base")
(include-book "writer")
(include-book "print-context")
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (enable acl2::arith-equiv-forwarding)))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system))))

(define vl-fmt-tilde-m-default (x &key (ps 'ps))
  (cond ((stringp x)
         (vl-print-modname x))
        ((vl-module-p x)
         (vl-pp-modulename-link-aux (vl-module->name x)
                                    (vl-module->origname x)))
        (t
         (vl-fmt-tilde-x x)))
  ///
  (defattach vl-fmt-tilde-m-fn vl-fmt-tilde-m-default-fn))

(define vl-fmt-tilde-w-default (x &key (ps 'ps))
  (cond ((stringp x)
         (vl-print-wirename x))
        ;; BOZO is there anything else this should print as a string?
        ;; ((vl-id-p x)
        ;;  (vl-print-wirename (vl-id->name x)))
        (t
         (vl-fmt-tilde-x x)))
  ///
  (defattach vl-fmt-tilde-w-fn vl-fmt-tilde-w-default-fn))




(defconst *vl-enable-unsafe-but-fast-printing* nil)

(defmacro vl-fmt-tilde-a-case (foo-p vl-print-foo)
  `(let ((ps (if (or unsafe-okp (,foo-p x))
                 ,(if (symbolp vl-print-foo)
                      `(,vl-print-foo x)
                    vl-print-foo)
               (vl-fmt-tilde-x x))))
     (mv ',foo-p ps)))



(define vl-fmt-tilde-a-aux (x &key (ps 'ps))
  :returns (mv (type "Used only for the so-called coverage proof.")
               (ps))
  :prepwork ((local (defthm hidexpr-p-when-stringp
                      (implies (stringp x)
                               (Vl-hidexpr-p x))
                      :hints(("Goal" :in-theory (enable vl-hidexpr-p)))))
             (local (defthm tag-when-vl-location-p
                      ;; Locations are special and don't have a sensible tag.
                      (implies (vl-location-p x)
                               (or (integerp (tag x))
                                   (consp (tag x))))
                      :rule-classes ((:type-prescription)
                                     (:forward-chaining))
                      :hints(("Goal" :in-theory (enable vl-location-p
                                                        vl-linecol-p
                                                        tag)))))
             (local (defthm hidexpr-p-when-vl-location-p
                      (implies (vl-location-p x)
                               (not (vl-hidexpr-p x)))
                      :hints(("Goal" :in-theory (enable vl-hidexpr-p vl-location-p))))))
  (b* ((unsafe-okp *vl-enable-unsafe-but-fast-printing*)
       ((when (atom x))
        (if (stringp x)
            (let ((ps (vl-pp-hidexpr x)))
              (mv 'vl-hidexpr-p ps))
          (let ((ps (vl-fmt-tilde-x x)))
            (mv nil ps))))
       ((when (vl-location-p x))
        ;; Locations use a special encoding to increase structure sharing, so
        ;; we don't get to just check them via tag.  Note that vl-location-p
        ;; is pretty darn cheap, so it's not terrible to check it first here.
        (let ((ps (vl-print-loc x)))
          (mv 'vl-location-p ps))))
    (case (tag x)
      ((:vl-special :vl-literal :vl-index :vl-unary :vl-binary
        :vl-qmark :vl-mintypmax :vl-concat :vl-multiconcat :vl-stream
        :vl-call :vl-cast :vl-inside :vl-tagged :vl-pattern :vl-eventexpr)
       (vl-fmt-tilde-a-case vl-expr-p vl-pp-origexpr))
      ((:vl-hidindex)
       (vl-fmt-tilde-a-case vl-hidindex-p vl-pp-hidindex))
      ((:vl-exprdist)
       (vl-fmt-tilde-a-case vl-exprdist-p vl-pp-exprdist))
      ((:vl-repetition)
       (vl-fmt-tilde-a-case vl-repetition-p vl-pp-repetition))
      ((:colon :paramscolon)
       (vl-fmt-tilde-a-case vl-scopeexpr-p vl-pp-scopeexpr))
      ((:vl-range)
       (vl-fmt-tilde-a-case vl-range-p vl-pp-range))
      ((:vl-nullstmt :vl-assignstmt :vl-deassignstmt :vl-callstmt
        :vl-disablestmt :vl-eventtriggerstmt :vl-casestmt :vl-ifstmt
        :vl-foreverstmt :vl-waitstmt :vl-repeatstmt :vl-whilestmt :vl-dostmt
        :vl-forstmt :vl-foreachstmt :vl-blockstmt :vl-timingstmt :vl-breakstmt
        :vl-continuestmt :vl-returnstmt :vl-assertstmt :vl-cassertstmt)
       (vl-fmt-tilde-a-case vl-stmt-p vl-pp-stmt))
      ((:vl-propcore :vl-propinst :vl-propthen :vl-proprepeat
        :vl-propassign :vl-propthroughout :vl-propclock :vl-propunary
        :vl-propbinary :vl-propalways :vl-propeventually :vl-propaccept
        :vl-propnexttime :vl-propif :vl-propcase)
       (vl-fmt-tilde-a-case vl-propexpr-p vl-pp-propexpr))
      ((:vl-propspec)
       (vl-fmt-tilde-a-case vl-propspec-p vl-pp-propspec))
      ((:vl-context)
       (vl-fmt-tilde-a-case vl-context1-p vl-pp-context-summary))
      ((:vl-regularport :vl-interfaceport :vl-portdecl :vl-assign
        :vl-alias :vl-vardecl :vl-paramdecl :vl-fundecl :vl-taskdecl
        :vl-modinst :vl-gateinst :vl-always :vl-initial :vl-final
        :vl-typedef :vl-fwdtypedef :vl-assertion :vl-cassertion
        :vl-property :vl-sequence :vl-clkdecl :vl-gclkdecl
        :vl-import :vl-dpiimport :vl-dpiexport :vl-bind :vl-class
        :vl-covergroup :vl-elabtask :vl-defaultdisable
        :vl-genarray :vl-genbegin :vl-genbase :vl-genif :vl-gencase :vl-genloop :vl-modport)
       (vl-fmt-tilde-a-case vl-ctxelement-p vl-pp-ctxelement-summary))
      ((:vl-genvar)
       (vl-fmt-tilde-a-case vl-genvar-p vl-pp-genvar))
      (:vl-ansi-portdecl
       (vl-fmt-tilde-a-case vl-ansi-portdecl-p vl-pp-ansi-portdecl))
      ;; ((:vl-plainarg)
      ;;  (vl-fmt-tilde-a-case vl-plainarg-p vl-pp-plainarg))
      ;; ((:vl-namedarg)
      ;;  (vl-fmt-tilde-a-case vl-namedarg-p vl-pp-namedarg))
      ((:vl-unsized-dimension :vl-star-dimension :vl-type-dimension :vl-queue-dimension)
       (vl-fmt-tilde-a-case vl-dimension-p vl-pp-dimension))
      ((:vl-enumitem)
       (vl-fmt-tilde-a-case vl-enumitem-p vl-pp-enumitem))
      ((:vl-coretype :vl-struct :vl-union :vl-enum :vl-usertype)
       (vl-fmt-tilde-a-case vl-datatype-p vl-pp-datatype))
      ((:vl-structmember)
       (vl-fmt-tilde-a-case vl-structmember-p vl-pp-structmember))
      ((:vl-fwdtypedef)
       (vl-fmt-tilde-a-case vl-fwdtypedef-p vl-pp-fwdtypedef))
      ((:vl-evatom)
       (vl-fmt-tilde-a-case vl-evatom-p vl-pp-evatom))
      ((:vl-eventcontrol)
       (vl-fmt-tilde-a-case vl-eventcontrol-p vl-pp-eventcontrol))
      ((:vl-delaycontrol)
       (vl-fmt-tilde-a-case vl-delaycontrol-p vl-pp-delaycontrol))
      ((:vl-repeat-eventcontrol)
       (vl-fmt-tilde-a-case vl-repeateventcontrol-p vl-pp-repeateventcontrol))
      ((:vl-module)
       (vl-fmt-tilde-a-case vl-module-p
         (vl-pp-modulename-link-aux (vl-module->name x)
                                    (vl-module->origname x))))
      (otherwise
       (if (vl-hidexpr-p x)
           (let ((ps (vl-pp-hidexpr x)))
             (mv 'vl-hidexpr-p ps))
         (let ((ps (vl-fmt-tilde-x x)))
           (mv nil ps))))))
  ///
  (local (defthm tag-when-vl-expr-p
           (implies (vl-expr-p x)
                    (equal (tag x) (vl-expr-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-expr-kind tag vl-expr-p)))))

  (local (defthm tag-when-vl-datatype-p
           (implies (vl-datatype-p x)
                    (equal (tag x) (vl-datatype-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-datatype-kind tag vl-datatype-p)))))

  (local (defthm tag-when-vl-stmt-p
           (implies (vl-stmt-p x)
                    (equal (tag x) (vl-stmt-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-stmt-kind tag vl-stmt-p)))))

  ;; (local (defthm tag-when-vl-hidexpr-p
  ;;          (implies (vl-hidexpr-p x)
  ;;                   (equal (tag x) (vl-hidexpr-kind x)))
  ;;          :rule-classes :forward-chaining
  ;;          :hints(("Goal" :in-theory (enable vl-hidexpr-kind tag vl-hidexpr-p)))))

  ;; (local (defthm tag-when-vl-scopeexpr-p
  ;;          (implies (vl-scopeexpr-p x)
  ;;                   (equal (tag x) (vl-scopeexpr-kind x)))
  ;;          :rule-classes :forward-chaining
  ;;          :hints(("Goal" :in-theory (enable vl-scopeexpr-kind tag vl-scopeexpr-p)))))

  (local (defthm tag-when-vl-propexpr-p
           (implies (vl-propexpr-p x)
                    (equal (tag x) (vl-propexpr-kind x)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-propexpr-kind tag vl-propexpr-p)))))

  ;; (local (defthm vl-hidexpr-p-means-not-vl-scopeexpr-p
  ;;          (implies (vl-hidexpr-p x)
  ;;                   (not (vl-scopeexpr-p x)))
  ;;          :rule-classes :forward-chaining
  ;;          :hints(("Goal" :expand ((vl-scopeexpr-p x)
  ;;                                  (vl-hidexpr-p x))))))

  (local (defthm not-hidexpr-when-non-string-atom
           (implies (and (atom x) (not (stringp x)))
                    (and (not (vl-hidexpr-p x))
                         (not (vl-scopeexpr-p x))))
           :hints(("Goal" :in-theory (enable vl-hidexpr-p
                                             vl-scopeexpr-p)))))

  (local (defthm not-hid/scopeexpr-when-location
           (and (implies (and (symbolp (tag x))
                              (consp x))
                         (not (vl-hidexpr-p x)))
                (implies (and (symbolp (tag x))
                              (consp x)
                              (not (equal (tag x) :colon))
                              (not (equal (tag x) :paramscolon)))
                         (not (vl-scopeexpr-p x))))
           :hints(("Goal" :in-theory (enable tag
                                             vl-scopeexpr-p
                                             vl-hidexpr-p
                                             vl-hidindex-p)
                   :expand ((vl-hidexpr-p x)
                            (vl-scopeexpr-p x))))))

  (local (defthm not-scopeexpr-when-not-colon-or-hidexpr
           (implies (and (not (vl-hidexpr-p x))
                         (not (Equal (tag x) :colon))
                         (not (Equal (tag x) :paramscolon)))
                    (not (vl-scopeexpr-p x)))
           :hints(("Goal" :in-theory (enable tag)
                   :expand ((vl-scopeexpr-p x))))))

  (local (in-theory (enable tag-reasoning)))

  (defrule vl-fmt-tilde-a-aux-coverage
    (b* (((mv type &) (vl-fmt-tilde-a-aux x)))
      (and (implies (vl-location-p x) (equal type 'vl-location-p))
           (implies (vl-expr-p x) (equal type 'vl-expr-p))
           (implies (vl-hidexpr-p x) (equal type 'vl-hidexpr-p))
           (implies (vl-scopeexpr-p x) (or (equal type 'vl-scopeexpr-p)
                                           (equal type 'vl-hidexpr-p)))
           (implies (vl-exprdist-p x) (equal type 'vl-exprdist-p))
           (implies (vl-range-p x) (equal type 'vl-range-p))
           (implies (vl-propexpr-p x) (equal type 'vl-propexpr-p))
           (implies (vl-propspec-p x) (equal type 'vl-propspec-p))
           (implies (vl-datatype-p x) (equal type 'vl-datatype-p))
           (implies (vl-structmember-p x) (equal type 'vl-structmember-p))
           (implies (vl-ctxelement-p x) (equal type 'vl-ctxelement-p))
           (implies (vl-enumitem-p x) (equal type 'vl-enumitem-p))
           (implies (vl-stmt-p x) (equal type 'vl-stmt-p))
           (implies (vl-evatom-p x) (equal type 'vl-evatom-p))
           (implies (vl-eventcontrol-p x) (equal type 'vl-eventcontrol-p))
           (implies (vl-delaycontrol-p x) (equal type 'vl-delaycontrol-p))
           (implies (vl-repeateventcontrol-p x) (equal type 'vl-repeateventcontrol-p))
           ))
    :rule-classes nil))

(define vl-fmt-tilde-a-default (x &key (ps 'ps))
  (b* (((mv ?type ps)
        (vl-fmt-tilde-a-aux x)))
    ps)
  ///
  (defattach vl-fmt-tilde-a-fn vl-fmt-tilde-a-default-fn))
