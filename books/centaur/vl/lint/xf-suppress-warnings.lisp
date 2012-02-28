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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

; VL Warning Suppression
;
; This is quick and dirty, but probably is actually a pretty effective and
; reasonable way to deal with suppressing unwanted warnings from VL-Lint.
;
; The basic idea is to stick attributes such as (* LINT_IGNORE *) into the
; source code, which with our comment syntax can be done using the form //@VL
; LINT_IGNORE, or similar.  We then look for these attributes to decide whether
; to suppress a warning.
;
; For convenience we treat LINT_IGNORE directives in a case-insensitive way and
; treat _ interchangeably with -.  This is useful because the Verilog user has
; to use _ since these are attribute names and hence must be valid identifiers.
;
; We let the user write things like LINT_IGNORE_VL_WARN_ODDEXPR, or, more
; conveniently, LINT_IGNORE_ODDEXPR, by just "mashing" the tail of what they
; write by throwing away any leading VL_ or VL_WARN_ part.  By convention a
; plain LINT_IGNORE with no further information means just ignore all warnings.

(defund vl-lint-ignore-att-p (x)
  ;; lint-ignore... or lint_ignore..., case insensitive
  (declare (xargs :guard (stringp x)))
  (let ((x (str::strsubst "-" "_" x)))
    (str::istrprefixp "lint_ignore" x)))

(defund vl-lint-ignore-att-mash (x)
  (declare (xargs :guard (and (stringp x)
                              (vl-lint-ignore-att-p x))))
  (b* ((x (str::strsubst "-" "_" x))
       ((when (equal (length x) (length "lint_ignore")))
        ;; The empty string will mean ignore any warning.
        "")
       (x (str::upcase-string x))
       (x (ec-call (subseq x (length "lint_ignore") nil)))
       (x (if (str::strprefixp "_" x)
              (ec-call (subseq x 1 nil))
            x))
       (x (if (str::strprefixp "VL_" x)
              (ec-call (subseq x 3 nil))
            x))
       (x (if (str::strprefixp "WARN_" x)
              (ec-call (subseq x 5 nil))
            x)))
    x))

(defund vl-warning-type-mash (x)
  (declare (xargs :guard (symbolp x)))
  (b* ((name (symbol-name x))
       (name (str::strsubst "-" "_" name))
       (name (if (str::strprefixp "VL_" name)
                 (ec-call (subseq name 3 nil))
               name))
       (name (if (str::strprefixp "WARN_" name)
                 (ec-call (subseq name 5 nil))
               name)))
    name))

(defthm stringp-of-vl-warning-type-mash
  (stringp (vl-warning-type-mash x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-warning-type-mash))))

(defund vl-lint-attname-says-ignore (attname mashed-warning-type)
  (declare (xargs :guard (and (stringp attname)
                              (stringp mashed-warning-type))))
  (b* (((unless (vl-lint-ignore-att-p attname))
        nil)
       (mashed-att (vl-lint-ignore-att-mash attname))
       ((when (equal mashed-att ""))
        ;; Ignore everything!
        t))
    ;; Otherwise, only ignore certain warning types
    (equal mashed-att mashed-warning-type)))

(assert!
 (let ((wmash (vl-warning-type-mash :vl-warn-oddexpr)))
   (and (vl-lint-attname-says-ignore "lint_ignore" wmash)
        (vl-lint-attname-says-ignore "lint_ignore_" wmash)
        (vl-lint-attname-says-ignore "LINT_IGNORE" wmash)
        (vl-lint-attname-says-ignore "LINT_IGNORE_ODDEXPR" wmash)
        (vl-lint-attname-says-ignore "LINT_IGNORE_oddexpr" wmash)
        (vl-lint-attname-says-ignore "LINT_IGNORE_VL_ODDEXPR" wmash)
        (vl-lint-attname-says-ignore "LiNt_IgNoRe_Vl_WaRn_OdDeXpR" wmash)
        (not (vl-lint-attname-says-ignore "LINT_IGNORE_FOO" wmash))
        (not (vl-lint-attname-says-ignore "LINT_IGNORE_VL_FOO" wmash)))))

(defund vl-lint-atts-say-ignore (atts mashed-warning-type)
  (declare (xargs :guard (and (vl-atts-p atts)
                              (stringp mashed-warning-type))))
  (if (atom atts)
      nil
    (or (vl-lint-attname-says-ignore (caar atts) mashed-warning-type)
        (vl-lint-atts-say-ignore (cdr atts) mashed-warning-type))))


; So, where do we look for these attributes?  Most VL warnings include a
; particular module element among their args that gives a context for the
; warning.  For instance a truncation warning might say that it happens in a
; certain assignment.  It seems basically reasonable, then, to look in the
; arguments of the warning and look for attributes that say to ignore the
; warning, and most of the time this should pretty much just work.

(defund vl-lint-scan-for-ignore (x mwtype)
  (declare (xargs :guard (stringp mwtype)))
  (b* (((when (atom x))
        nil)
       ((when (symbolp (car x)))
        (if (eq (car x) :vl-module)
            ;; Don't descend into whole modules
            nil
          (or
           ;; Recognize certain constructs that have attributes
           (case (car x)
             (:vl-nonatom
              (and (vl-nonatom-p x)
                   (vl-expr-p x)
                   (vl-lint-atts-say-ignore (vl-nonatom->atts x) mwtype)))
             (:vl-netdecl      (and (vl-netdecl-p x)       (vl-lint-atts-say-ignore (vl-netdecl->atts x)       mwtype)))
             (:vl-assign       (and (vl-assign-p x)        (vl-lint-atts-say-ignore (vl-assign->atts x)        mwtype)))
             (:vl-modinst      (and (vl-modinst-p x)       (vl-lint-atts-say-ignore (vl-modinst->atts x)       mwtype)))
             (:vl-gateinst     (and (vl-gateinst-p x)      (vl-lint-atts-say-ignore (vl-gateinst->atts x)      mwtype)))
             (:vl-portdecl     (and (vl-portdecl-p x)      (vl-lint-atts-say-ignore (vl-portdecl->atts x)      mwtype)))
             (:vl-vardecl      (and (vl-vardecl-p x)       (vl-lint-atts-say-ignore (vl-vardecl->atts x)       mwtype)))
             (:vl-regdecl      (and (vl-regdecl-p x)       (vl-lint-atts-say-ignore (vl-regdecl->atts x)       mwtype)))
             (:vl-eventdecl    (and (vl-eventdecl-p x)     (vl-lint-atts-say-ignore (vl-eventdecl->atts x)     mwtype)))
             (:vl-paramdecl    (and (vl-paramdecl-p x)     (vl-lint-atts-say-ignore (vl-paramdecl->atts x)     mwtype)))
             (:vl-fundecl      (and (vl-fundecl-p x)       (vl-lint-atts-say-ignore (vl-fundecl->atts x)       mwtype)))
             (:vl-funinput     (and (vl-funinput-p x  )    (vl-lint-atts-say-ignore (vl-funinput->atts x)      mwtype)))
             (:vl-always       (and (vl-always-p x)        (vl-lint-atts-say-ignore (vl-always->atts x)        mwtype)))
             (:vl-initial      (and (vl-initial-p x)       (vl-lint-atts-say-ignore (vl-initial->atts x)       mwtype)))
             (:vl-plainarg     (and (vl-plainarg-p x)      (vl-lint-atts-say-ignore (vl-plainarg->atts x)      mwtype)))
             (:vl-namedarg     (and (vl-namedarg-p x)      (vl-lint-atts-say-ignore (vl-namedarg->atts x)      mwtype)))
             (:vl-assignstmt   (and (vl-assignstmt-p x)    (vl-lint-atts-say-ignore (vl-assignstmt->atts x)    mwtype)))
             (:vl-compoundstmt (and (vl-compoundstmt-p x)  (vl-lint-atts-say-ignore (vl-compoundstmt->atts x)  mwtype)))
             (:vl-deassignstmt (and (vl-deassignstmt-p x)  (vl-lint-atts-say-ignore (vl-deassignstmt->atts x)  mwtype)))
             (:vl-enablestmt   (and (vl-enablestmt-p x)    (vl-lint-atts-say-ignore (vl-enablestmt->atts x)    mwtype)))
             (:vl-enablestmt   (and (vl-enablestmt-p x)    (vl-lint-atts-say-ignore (vl-enablestmt->atts x)    mwtype)))
             (:vl-nullstmt     (and (vl-nullstmt-p x)      (vl-lint-atts-say-ignore (vl-nullstmt->atts x)      mwtype)))
             (:vl-eventtriggerstmt
              (and (vl-eventtriggerstmt-p x)
                   (vl-lint-atts-say-ignore (vl-eventtriggerstmt->atts x) mwtype)))
             (otherwise nil))
           ;; Just because we didn't find it in the atts of this whole object
           ;; doesn't mean we want to necessarily stop looking.  let's keep
           ;; looking down, so that if there's an ignore decl inside an
           ;; expression inside this element, we'll still honor it.  We don't
           ;; need to descend into the CAR since it's just a symbol.
           (vl-lint-scan-for-ignore (cdr x) mwtype)))))
    (or (vl-lint-scan-for-ignore (car x) mwtype)
        (vl-lint-scan-for-ignore (cdr x) mwtype))))

(defsection vl-lint-suppress-warnings

  (defund vl-lint-suppress-warnings (x)
    (declare (xargs :guard (vl-warninglist-p x)))
    (b* (((when (atom x))
          nil)
         ((vl-warning x1) (car x))
         ((when (vl-lint-scan-for-ignore x1.args (vl-warning-type-mash x1.type)))
          (vl-lint-suppress-warnings (cdr x))))
      (cons (car x) (vl-lint-suppress-warnings (cdr x)))))

  (local (in-theory (enable vl-lint-suppress-warnings)))

  (defthm vl-warninglist-p-of-vl-lint-suppress-warings
    (implies (vl-warninglist-p x)
             (vl-warninglist-p (vl-lint-suppress-warnings x)))))



(defsection vl-module-suppress-lint-warnings

  (defund vl-module-suppress-lint-warnings (x)
    (declare (xargs :guard (vl-module-p x)))
    (change-vl-module x
                      :warnings (vl-lint-suppress-warnings (vl-module->warnings x))))

  (local (in-theory (enable vl-module-suppress-lint-warnings)))

  (defthm vl-module-p-of-vl-module-suppress-lint-warnings
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-suppress-lint-warnings x))))

  (defthm vl-module->name-of-vl-module-suppress-lint-warnings
    (equal (vl-module->name (vl-module-suppress-lint-warnings x))
           (vl-module->name x))))


(defsection vl-modulelist-suppress-lint-warnings

  (defprojection vl-modulelist-suppress-lint-warnings (x)
    (vl-module-suppress-lint-warnings x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (defthm vl-modulelist->names-of-vl-modulelist-suppress-lint-warnings
    (equal (vl-modulelist->names (vl-modulelist-suppress-lint-warnings x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))
