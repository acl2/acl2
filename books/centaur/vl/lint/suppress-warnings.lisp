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
(include-book "../parsetree")
(include-book "../mlib/stmt-tools")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "std/testing/assert" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defsection lint-warning-suppression
  :parents (vl-lint warnings)
  :short "An attribute- mechanism for suppressing particular @(see warnings)
when using @(see vl-lint)."

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

(local (defthm char-of-str-fix
         (equal (char (str-fix x) n)
                (char x n))
         :hints(("Goal" :in-theory (enable str-fix)))))

(local (defthm strprefixp-impl-of-str-fix
         (equal (str::strprefixp-impl a (str-fix x) m n oldl xl)
                (str::strprefixp-impl a x m n oldl xl))
         :hints(("Goal" :in-theory (e/d ((:i str::strprefixp-impl)) (char (force) (tau-system)))
                 :induct (str::strprefixp-impl a x m n oldl xl)
                 :expand ((:free (a x) (str::strprefixp-impl a x m n oldl xl))))
                (and stable-under-simplificationp
                     '(:expand ((:free (x) (str::strprefixp-impl a x 1 1 oldl xl))))))))

(local (defthm strsubst-aux-of-str-fix
         (equal (str::strsubst-aux a b (str-fix x) n xl oldl acc)
                (str::strsubst-aux a b x n xl oldl acc))
         :hints(("Goal" :in-theory (e/d ((:i str::strsubst-aux)) (char (force) (tau-system)))
                 :induct (str::strsubst-aux a b x n xl oldl acc)
                 :expand ((:free (x) (str::strsubst-aux a b x n xl oldl acc)))))))

(local (defthm strsubst-of-str-fix
         (equal (str::strsubst a b (str-fix x))
                (str::strsubst a b x))
         :hints(("Goal" :in-theory (e/d (str::strsubst))
                 :do-not-induct t))))

(define vl-lint-ignore-att-mash ((x stringp))
  :guard (vl-lint-ignore-att-p x)
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

(encapsulate
  (((vl-lint-suppress-warnings-att-compare * *) => *
    :formals (mashed-att mashed-warning-type)
    :guard (and (stringp mashed-att)
                (stringp mashed-warning-type))))

  (local (defun vl-lint-suppress-warnings-att-compare (mashed-att mashed-warning-type)
           (declare (xargs :guard (and (stringp mashed-att)
                                       (stringp mashed-warning-type))))
           (str::istrprefixp mashed-att mashed-warning-type)))

  (defthm booleanp-of-vl-lint-suppress-warnings-att-compare
    (booleanp (vl-lint-suppress-warnings-att-compare mashed-att mashed-warning-type))
    :rule-classes :type-prescription)

  (fty::deffixequiv vl-lint-suppress-warnings-att-compare
    :args ((mashed-att stringp) (mashed-warning-type stringp))))

(define vl-lint-suppress-warnings-att-compare-default ((mashed-att stringp)
                                                       (mashed-warning-type stringp))
  (str::istrprefixp mashed-att mashed-warning-type))

(defattach vl-lint-suppress-warnings-att-compare vl-lint-suppress-warnings-att-compare-default)

(define vl-lint-attname-says-ignore ((attname stringp)
                                     (mashed-warning-type stringp))
  :returns (ignorep booleanp :rule-classes :type-prescription)
  (b* (((unless (vl-lint-ignore-att-p attname))
        nil)
       (mashed-att (vl-lint-ignore-att-mash attname)))
    (vl-lint-suppress-warnings-att-compare mashed-att mashed-warning-type))
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
  :returns (ignorep booleanp :rule-classes :type-prescription)
  :measure (len (vl-atts-fix atts))
  (b* ((atts (vl-atts-fix atts)))
    (if (atom atts)
        nil
      (or (vl-lint-attname-says-ignore (caar atts) mashed-warning-type)
          (vl-lint-atts-say-ignore (cdr atts) mashed-warning-type)))))

(fty::defvisitor-template vl-lint-scan-for-ignore  ((x :object)
                                                    (mwtype stringp))
  :returns (ignorep (:join (or ignorep1 ignorep)
                     :tmp-var ignorep1
                     :initial nil)
                    booleanp :rule-classes :type-prescription)
  :type-fns ((vl-atts vl-lint-atts-say-ignore))
  :fnname-template <type>-scan-for-ignore)

(set-bogus-measure-ok t)

(fty::defvisitors vl-lint-scan-for-ignore-genelement
  :template vl-lint-scan-for-ignore
  :types (vl-genelement vl-context1))



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
          ;; Recognize certain constructs that have attributes
          (case (car x)
            ((:vl-special
              :vl-literal
              :vl-index
              :vl-unary
              :vl-binary
              :vl-qmark
              :vl-mintypmax
              :vl-concat
              :vl-multiconcat
              :vl-stream
              :vl-call
              :vl-cast
              :vl-inside
              :vl-tagged
              :vl-pattern)
             (and (vl-expr-p x) (vl-expr-scan-for-ignore x mwtype)))
            (:vl-assign       (and (vl-assign-p x)        (vl-assign-scan-for-ignore x        mwtype)))
            (:vl-modinst      (and (vl-modinst-p x)       (vl-modinst-scan-for-ignore x       mwtype)))
            (:vl-gateinst     (and (vl-gateinst-p x)      (vl-gateinst-scan-for-ignore x      mwtype)))
            (:vl-portdecl     (and (vl-portdecl-p x)      (vl-portdecl-scan-for-ignore x      mwtype)))
            (:vl-vardecl      (and (vl-vardecl-p x)       (vl-vardecl-scan-for-ignore x       mwtype)))
            (:vl-paramdecl    (and (vl-paramdecl-p x)     (vl-paramdecl-scan-for-ignore x     mwtype)))
            (:vl-fundecl      (and (vl-fundecl-p x)       (vl-fundecl-scan-for-ignore x       mwtype)))
            (:vl-taskdecl     (and (vl-taskdecl-p x)      (vl-taskdecl-scan-for-ignore x      mwtype)))
            (:vl-always       (and (vl-always-p x)        (vl-always-scan-for-ignore x        mwtype)))
            (:vl-initial      (and (vl-initial-p x)       (vl-initial-scan-for-ignore x       mwtype)))
            (:vl-plainarg     (and (vl-plainarg-p x)      (vl-plainarg-scan-for-ignore x      mwtype)))
            (:vl-namedarg     (and (vl-namedarg-p x)      (vl-namedarg-scan-for-ignore x      mwtype)))

            (:vl-context      (and (vl-context1-p x)      (vl-context1-scan-for-ignore x      mwtype)))

            ((:vl-nullstmt :vl-assignstmt :vl-deassignstmt
              :vl-callstmt :vl-disablestmt :vl-eventtriggerstmt
              :vl-casestmt :vl-ifstmt :vl-foreverstmt :vl-waitstmt
              :vl-repeatstmt :vl-whilestmt :vl-forstmt :vl-foreachstmt
              :vl-breakstmt :vl-continuestmt :vl-blockstmt
              :vl-timingstmt :vl-returnstmt :vl-assertstmt
              :vl-cassertstmt)
             (and (vl-stmt-p x)
                  (vl-stmt-scan-for-ignore x mwtype)))

            (otherwise nil)))))
    (or (vl-lint-scan-for-ignore (car x) mwtype)
        (vl-lint-scan-for-ignore (cdr x) mwtype))))

(define vl-lint-suppress-warnings ((x vl-warninglist-p))
  :returns (new-x vl-warninglist-p)
  (b* (((when (atom x))
        nil)
       ((vl-warning x1) (car x))
       (type (vl-warning-type-mash x1.type))
       ((when (or (vl-lint-scan-for-ignore x1.context type)
                  (vl-lint-scan-for-ignore x1.args type)))
        (cons (change-vl-warning (car x) :suppressedp t)
              (vl-lint-suppress-warnings (cdr x)))))
    (cons (vl-warning-fix (car x))
          (vl-lint-suppress-warnings (cdr x)))))




(defmacro def-vl-suppress-lint-warnings (name)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
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
(def-vl-suppress-lint-warnings class)
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
                      :classes    (vl-classlist-suppress-lint-warnings     x.classes)
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
  (b* ((mksym-package-symbol (pkg-witness "VL"))
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
(def-vl-lint-ignoreall class)
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
                      :classes    (vl-classlist-lint-ignoreall     x.classes    mashed-ignore-list)
                      :packages   (vl-packagelist-lint-ignoreall   x.packages   mashed-ignore-list)
                      :configs    (vl-configlist-lint-ignoreall    x.configs    mashed-ignore-list))))
