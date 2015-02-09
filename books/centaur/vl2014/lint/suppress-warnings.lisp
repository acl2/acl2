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
(include-book "../parsetree")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection lint-warning-suppression
  :parents (lint warnings)
  :short "An attribute- mechanism for suppressing particular @(see warnings)
when using @(see lint)."

  :long "<p>This is quick and dirty, but probably is actually a pretty
effective and reasonable way to deal with suppressing unwanted warnings from
VL-Lint.</p>

<p>The basic idea is to stick attributes such as @('(* LINT_IGNORE *)') into
the source code, which with our comment syntax can be done using the form
@('//@VL LINT_IGNORE'), or similar.  We then look for these attributes to
decide whether to suppress a warning.</p>

<p>For convenience we treat @('LINT_IGNORE') directives in a case-insensitive
way and treat _ interchangeably with -.  This is useful because the Verilog
user typically has to use _ since these are attribute names and hence must be
valid identifiers.</p>

<p>We let the user write things like @('LINT_IGNORE_VL_WARN_ODDEXPR'), or, more
conveniently, @('LINT_IGNORE_ODDEXPR'), by just \"mashing\" the tail of what
they write by throwing away any leading @('VL_') or @('VL_WARN_') part.  By
convention a plain @('LINT_IGNORE') with no further information means just
ignore all warnings.</p>")

(local (xdoc::set-default-parents lint-warning-suppression))


(define vl-mash-warning-string
  :short "Do basic string mashing to allow the user to refer to warnings in
either upper or lower case, treating - and _ as equivalent, and with or without
@('vl_warn_') prefixes."
  ((x stringp))
  :returns (new-x stringp :rule-classes :type-prescription)
  (b* ((x (str::upcase-string x))
       (x (str::strsubst "-" "_" x))
       (x (if (str::strprefixp "_" x)
              (subseq x 1 nil)
            x))
       (x (if (str::strprefixp "VL_" x)
              (ec-call (subseq x 3 nil))
            x))
       (x (if (str::strprefixp "WARN_" x)
              (ec-call (subseq x 5 nil))
            x)))
    x))

(defprojection vl-mash-warning-strings ((x string-listp))
  :returns (new-x string-listp)
  (vl-mash-warning-string x))

(define vl-lint-ignore-att-p ((x stringp))
  :short "Recognize strings that start with lint-ignore or lint_ignore, case
          insensitive"
  (b* ((x (string-fix x))
       (x (str::strsubst "-" "_" x)))
    (str::istrprefixp "lint_ignore" x)))

(define vl-lint-ignore-att-mash ((x (and (stringp x)
                                         (vl-lint-ignore-att-p x))))
  ;; Note: the guard ensures that x starts with lint_ignore
  (b* ((x (str::strsubst "-" "_" x))
       ((when (equal (length x) (length "lint_ignore")))
        ;; The empty string after lint_ignore means, "ignore all warnings"
        "")
       (x (ec-call (subseq x (length "lint_ignore") nil))))
    (vl-mash-warning-string x)))

(define vl-warning-type-mash ((x symbolp))
  :returns (mashed stringp :rule-classes :type-prescription)
  (vl-mash-warning-string (symbol-name x)))

(define vl-lint-attname-says-ignore ((attname stringp)
                                     (mashed-warning-type stringp))
  :returns (ignorep booleanp :rule-classes :type-prescription)
  :hooks nil
  (b* (((unless (vl-lint-ignore-att-p attname))
        nil)
       (mashed-att (vl-lint-ignore-att-mash attname))
       ((when (equal mashed-att ""))
        ;; Ignore everything!
        t))
    ;; Otherwise, only ignore certain warning types
    (str::istrprefixp mashed-att mashed-warning-type))
  ///
  (local
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
           (not (vl-lint-attname-says-ignore "LINT_IGNORE_VL_FOO" wmash))))))

  (local
   (assert!
    (let ((wmash (vl-warning-type-mash :vl-warn-fussy-size-warning-3)))
      (and (vl-lint-attname-says-ignore "lint_ignore" wmash)
           (vl-lint-attname-says-ignore "lint_ignore_fussy" wmash)
           (vl-lint-attname-says-ignore "LINT_IGNORE_FUSSY_SIZE" wmash)
           (vl-lint-attname-says-ignore "LINT_IGNORE_FUSSY_SIZE_WARNING" wmash)
           (vl-lint-attname-says-ignore "LINT_IGNORE_FUSSY_SIZE_WARNING-3" wmash))))))

(define vl-lint-atts-say-ignore ((atts vl-atts-p)
                                 (mashed-warning-type stringp))
  :hooks nil
  :returns (ignorep booleanp :rule-classes :type-prescription)
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

(define vl-lint-scan-for-ignore
  ((x "Arbitrary stuff that might occur in a warning's args.")
   (mwtype stringp))
  :hooks nil
  :returns (ignorep booleanp :rule-classes :type-prescription)
  (b* (((when (atom x))
        nil)
       ((when (symbolp (car x)))
        (if (eq (car x) :vl-module)
            ;; Don't descend into whole modules
            nil
          (or
           ;; Recognize certain constructs that have attributes
           (case (car x)
             (:nonatom
              (and (vl-expr-p x)
                   (eq (vl-expr-kind x) :nonatom)
                   (vl-lint-atts-say-ignore (vl-nonatom->atts x) mwtype)))
             (:vl-assign       (and (vl-assign-p x)        (vl-lint-atts-say-ignore (vl-assign->atts x)        mwtype)))
             (:vl-modinst      (and (vl-modinst-p x)       (vl-lint-atts-say-ignore (vl-modinst->atts x)       mwtype)))
             (:vl-gateinst     (and (vl-gateinst-p x)      (vl-lint-atts-say-ignore (vl-gateinst->atts x)      mwtype)))
             (:vl-portdecl     (and (vl-portdecl-p x)      (vl-lint-atts-say-ignore (vl-portdecl->atts x)      mwtype)))
             (:vl-vardecl      (and (vl-vardecl-p x)       (vl-lint-atts-say-ignore (vl-vardecl->atts x)       mwtype)))
             (:vl-paramdecl    (and (vl-paramdecl-p x)     (vl-lint-atts-say-ignore (vl-paramdecl->atts x)     mwtype)))
             (:vl-fundecl      (and (vl-fundecl-p x)       (vl-lint-atts-say-ignore (vl-fundecl->atts x)       mwtype)))
             (:vl-taskdecl     (and (vl-taskdecl-p x)      (vl-lint-atts-say-ignore (vl-taskdecl->atts x)      mwtype)))
             (:vl-always       (and (vl-always-p x)        (vl-lint-atts-say-ignore (vl-always->atts x)        mwtype)))
             (:vl-initial      (and (vl-initial-p x)       (vl-lint-atts-say-ignore (vl-initial->atts x)       mwtype)))
             (:vl-plainarg     (and (vl-plainarg-p x)      (vl-lint-atts-say-ignore (vl-plainarg->atts x)      mwtype)))
             (:vl-namedarg     (and (vl-namedarg-p x)      (vl-lint-atts-say-ignore (vl-namedarg->atts x)      mwtype)))


             ((:vl-nullstmt :vl-assignstmt :vl-deassignstmt
               :vl-enablestmt :vl-disablestmt :vl-eventtriggerstmt
               :vl-casestmt :vl-ifstmt :vl-foreverstmt :vl-waitstmt
               :vl-whilestmt :vl-forstmt :vl-blockstmt :vl-repeatstmt :vl-timingstmt)
              (and (vl-stmt-p x)
                   (vl-lint-atts-say-ignore (vl-stmt->atts x) mwtype)))

             (otherwise nil))
           ;; Just because we didn't find it in the atts of this whole object
           ;; doesn't mean we want to necessarily stop looking.  let's keep
           ;; looking down, so that if there's an ignore decl inside an
           ;; expression inside this element, we'll still honor it.  We don't
           ;; need to descend into the CAR since it's just a symbol.
           (vl-lint-scan-for-ignore (cdr x) mwtype)))))
    (or (vl-lint-scan-for-ignore (car x) mwtype)
        (vl-lint-scan-for-ignore (cdr x) mwtype))))

(define vl-lint-suppress-warnings ((x vl-warninglist-p))
  :returns (new-x vl-warninglist-p)
  (b* (((when (atom x))
        nil)
       ((vl-warning x1) (car x))
       ((when (vl-lint-scan-for-ignore x1.args (vl-warning-type-mash x1.type)))
        (vl-lint-suppress-warnings (cdr x))))
    (cons (vl-warning-fix (car x))
          (vl-lint-suppress-warnings (cdr x)))))




(defmacro def-vl-suppress-lint-warnings (name)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (elem-fn        (mksym 'vl- name '-suppress-lint-warnings))
       (list-fn        (mksym 'vl- name 'list-suppress-lint-warnings))
       (elem-p         (mksym 'vl- name '-p))
       (list-p         (mksym 'vl- name 'list-p))
       (elem->warnings (mksym 'vl- name '->warnings))
       (change-elem    (mksym 'change-vl- name)))
    `(progn
       (define ,elem-fn ((x ,elem-p))
         :parents (vl-design-suppress-lint-warnings)
         :returns (new-x ,elem-p)
         (,change-elem x :warnings (vl-lint-suppress-warnings (,elem->warnings x))))
       (defprojection ,list-fn ((x ,list-p))
         :parents (vl-design-suppress-lint-warnings)
         :returns (new-x ,list-p)
         (,elem-fn x)))))

(def-vl-suppress-lint-warnings module)
(def-vl-suppress-lint-warnings udp)
(def-vl-suppress-lint-warnings interface)
(def-vl-suppress-lint-warnings program)
(def-vl-suppress-lint-warnings package)
(def-vl-suppress-lint-warnings config)

(define vl-design-suppress-lint-warnings ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x
                      :mods       (vl-modulelist-suppress-lint-warnings    x.mods)
                      :udps       (vl-udplist-suppress-lint-warnings       x.udps)
                      :interfaces (vl-interfacelist-suppress-lint-warnings x.interfaces)
                      :programs   (vl-programlist-suppress-lint-warnings   x.programs)
                      :packages   (vl-packagelist-suppress-lint-warnings   x.packages)
                      :configs    (vl-configlist-suppress-lint-warnings    x.configs))))



(define vl-warninglist-lint-ignoreall
  :short "Globally suppress certain kinds of warnings."
  ((x vl-warninglist-p)
   (mashed-ignore-list string-listp))
  :returns (new-warnings vl-warninglist-p)
  (b* ((mashed-ignore-list (string-list-fix mashed-ignore-list))
       ((when (atom x))
        nil)
       (type1 (vl-warning->type (car x)))
       (type1-mash (vl-warning-type-mash type1))
       ((when (member-equal type1-mash mashed-ignore-list))
        (vl-warninglist-lint-ignoreall (cdr x) mashed-ignore-list)))
    (cons (vl-warning-fix (car x))
          (vl-warninglist-lint-ignoreall (cdr x) mashed-ignore-list))))


(defmacro def-vl-lint-ignoreall (name)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (elem-fn        (mksym 'vl- name '-lint-ignoreall))
       (list-fn        (mksym 'vl- name 'list-lint-ignoreall))
       (elem-p         (mksym 'vl- name '-p))
       (list-p         (mksym 'vl- name 'list-p))
       (elem->warnings (mksym 'vl- name '->warnings))
       (change-elem    (mksym 'change-vl- name)))
    `(progn
       (define ,elem-fn ((x                  ,elem-p)
                         (mashed-ignore-list string-listp))
         :parents (vl-design-lint-ignoreall)
         :returns (new-x ,elem-p)
         (,change-elem x :warnings (vl-warninglist-lint-ignoreall (,elem->warnings x)
                                                                  mashed-ignore-list)))
       (defprojection ,list-fn ((x                  ,list-p)
                                (mashed-ignore-list string-listp))
         :parents (vl-design-lint-ignoreall)
         :returns (new-x ,list-p)
         (,elem-fn x mashed-ignore-list)))))

(def-vl-lint-ignoreall module)
(def-vl-lint-ignoreall udp)
(def-vl-lint-ignoreall interface)
(def-vl-lint-ignoreall program)
(def-vl-lint-ignoreall package)
(def-vl-lint-ignoreall config)

(define vl-design-lint-ignoreall
  ((x                vl-design-p)
   (user-ignore-list string-listp
                     "A list of user-level ignore strings.  We'll mash these
                      first.  That is, the user can say all kinds of things,
                      like \"oddexpr\" or \"vl_oddexpr\" or \"warn_oddexpr\"
                      or \"warn-oddexpr\" etc., to suppress oddexpr warnings."))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (mashed-ignore-list (vl-mash-warning-strings user-ignore-list)))
    (change-vl-design x
                      :mods       (vl-modulelist-lint-ignoreall    x.mods       mashed-ignore-list)
                      :udps       (vl-udplist-lint-ignoreall       x.udps       mashed-ignore-list)
                      :interfaces (vl-interfacelist-lint-ignoreall x.interfaces mashed-ignore-list)
                      :programs   (vl-programlist-lint-ignoreall   x.programs   mashed-ignore-list)
                      :packages   (vl-packagelist-lint-ignoreall   x.packages   mashed-ignore-list)
                      :configs    (vl-configlist-lint-ignoreall    x.configs    mashed-ignore-list))))
