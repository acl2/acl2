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
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "oslib/ls" :dir :system)
(local (include-book "../util/arithmetic"))

(defsection file-layout
  :parents (server)
  :short "Where we look for translation data."

  :long "<p>The constant @(see *vls-root*) defines the root directory for our
translation data.</p>

<p>Each subdirectory of this directory is called a <b>base</b>.  At Centaur, we
typically run the translator once per day, and we introduce a new base for each
day's translations.  That is, the base <tt>2010-05-31</tt> contains the
translations from May 31, 2010, etc.</p>

<p>Note: as a special convenience, if the name of a base begins with
<tt>_temp_</tt>, we regard it as currently being generated and do not include
it in our file scans.  Our translation scripts put everything into a directory
like <tt>_temp_2010-05-31</tt>, then finally rename this directory to
<tt>2010-05-31</tt> when they're done.</p>

<p>Each base should contain a collection of subdirectories called
<b>models</b>.  Each model directory contains files like <tt>model.sao</tt> and
<tt>esims.sao</tt>, which are created by the @('vl model') command.  Having
multiple models is useful when you are translating many different chips.</p>

<p>Given <tt>*vls-root*</tt>, the name of a particular base and model are
sufficient for identifying where a particular translation exists on the
disk.</p>")

(local (xdoc::set-default-parents file-layout))

(defsection *vls-root*
  :short "File system path that says where to look for translations."

  :long "<p>This constant should be the name of a directory, with no trailing
slash, e.g., <tt>/n/fv2/translations</tt>.</p>"

  (defconst *vls-root* "/n/fv2/translations"))

(define set-vls-root ((new-root stringp))
  :short "Smash @(see *vls-root*) with something new."
  :ignore-ok t
  (raise "Under the hood definition not installed."))

(define vls-datestr-p ((x stringp))
  :short "Recognize strings of the form @('YYYY-MM-DD*')."
  :guard-hints(("Goal" :in-theory (disable nth-when-zp)))
  (and (<= 10 (length x))
       (str::dec-digit-char-p (char x 0)) ;; y
       (str::dec-digit-char-p (char x 1)) ;; y
       (str::dec-digit-char-p (char x 2)) ;; y
       (str::dec-digit-char-p (char x 3)) ;; y
       (eql (char x 4) #\-)     ;; -
       (str::dec-digit-char-p (char x 5)) ;; m
       (str::dec-digit-char-p (char x 6)) ;; m
       (eql (char x 7) #\-)     ;; -
       (str::dec-digit-char-p (char x 8)) ;; d
       (str::dec-digit-char-p (char x 9)) ;; d
       ))

(define vls-filter-datestrs
  :short "Filter strings into datestrs and non-datestrs.  (See @(see vls-datestr-p)s)."
  ((x      "Strings to filter." string-listp)
   (dates  "Accumulator for datestrs." string-listp)
   (others "Accumulator for non-datestrs." string-listp))
  :returns (mv (dates string-listp :hyp :fguard)
               (others string-listp :hyp :fguard))
  (cond ((atom x)
         (mv dates others))
        ((vls-datestr-p (car x))
         (vls-filter-datestrs (cdr x) (cons (car x) dates) others))
        (t
         (vls-filter-datestrs (cdr x) dates (cons (car x) others)))))

(define vls-sort-bases ((x string-listp))
  :short "Put translations into a nice order."
  :returns (bases string-listp)
  (b* ((x (string-list-fix x))
       ((mv dates others) (vls-filter-datestrs x nil nil)))
      (append (mergesort others)
              (reverse (mergesort dates)))))




(defprod vl-tname
  :short "Location of a chip translation"
  :tag :vl-tname
  ((base  stringp :rule-classes :type-prescription)
   (model stringp :rule-classes :type-prescription)))

(deflist vl-tnamelist-p (x)
  (vl-tname-p x))

(defprojection vl-tnamelist-bases ((x vl-tnamelist-p))
  :returns (bases string-listp)
  (vl-tname->base x))

(defprojection vl-tnamelist-models ((x vl-tnamelist-p))
  :returns (models string-listp)
  (vl-tname->model x))

(define vl-tname-as-string ((x vl-tname-p))
  :returns (str stringp :rule-classes :type-prescription)
  ;; BOZO eventually consider properly encoding these
  (str::cat (vl-tname->base x) ":" (vl-tname->model x)))

(defprojection vl-tnamelist-as-strings ((x vl-tnamelist-p))
  :returns (strings string-listp)
  (vl-tname-as-string x))



(define vl-tnames-for-base ((base stringp)
                            (x    vl-tnamelist-p))
  :returns (tnames vl-tnamelist-p)
  (cond ((atom x)
         nil)
        ((equal base (vl-tname->base (car x)))
         (cons (vl-tname-fix (car x))
               (vl-tnames-for-base base (cdr x))))
        (t
         (vl-tnames-for-base base (cdr x)))))

(define vl-find-tname ((base  stringp)
                       (model stringp)
                       (x     vl-tnamelist-p))
  :returns (tname (equal (vl-tname-p tname)
                         (if tname t nil)))
  (cond ((atom x)
         nil)
        ((and (equal base (vl-tname->base (car x)))
              (equal model (vl-tname->model (car x))))
         (vl-tname-fix (car x)))
        (t
         (vl-find-tname base model (cdr x)))))

(define vl-tname-dir ((x vl-tname-p))
  :returns (dir stringp :rule-classes :type-prescription)
  (b* (((vl-tname x) x))
      (str::cat *vls-root* "/" x.base "/" x.model "/")))


(define vl-tname-xdat-file ((x vl-tname-p))
  :returns (path stringp :rule-classes :type-prescription)
  (str::cat (vl-tname-dir x) "model.sao"))

(defprojection vl-tnamelist-xdat-files ((x vl-tnamelist-p))
  :returns (paths string-listp)
  (vl-tname-xdat-file x))


;; Scanning for translations.

(local
 (encapsulate
  ()
  (local (defthm crock
           (implies (string-listp x)
                    (true-listp x))))

  (defthm true-listp-of-ls-files
    (true-listp (mv-nth 1 (oslib::ls-files path)))
    :rule-classes :type-prescription)))

(define vl-looks-like-legitimate-tname-p ((x vl-tname-p) state)
  :returns (mv (legitp booleanp :rule-classes :type-prescription)
               (state  state-p1 :hyp (force (state-p1 state))))
  :short "Return true if the given translation directory (1) includes both
          model.sao and model.sao.ver files, and (2) the model is compatible
          with this version of VL."
  (b* ((tdir (vl-tname-dir x))
       ((mv err files state)
        (oslib::ls-files tdir))
       ((when err)
        (cw "; NOTE: Error listing ~x0: ~@1~%" tdir err)
        (mv nil state))
       ((unless (and (member-equal "model.sao" files)
                     (member-equal "model.sao.ver" files)))
        ;; (cw "Skip ~s0 (missing model files).~%" tdir)
        (mv nil state))
       (verfile        (oslib::catpath tdir "model.sao.ver"))
       ((mv ver state) (acl2::read-file-as-string verfile state))
       ((unless ver)
        ;; (cw "Skip ~s0 (can't read ~x1).~%" tdir verfile)
        (mv nil state))
       (found  (str::trim ver))
       (expect (str::trim *vl-current-syntax-version*))
       ((unless (equal found expect))
        ;; (cw "Skip ~x0 (version ~x1, expected ~x2).~%" tdir found expect)
        (mv nil state)))
    ;; (cw "Found ~x0, right version.~%" tdir)
    (mv t state)))

(define vl-remove-illegitimate-tnames ((x vl-tnamelist-p)
                                       (state))
  :returns (mv (legitimate vl-tnamelist-p)
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom x))
        (mv nil state))
       ((mv car-legitp state) (vl-looks-like-legitimate-tname-p (car x) state))
       ((mv cdr-prime state)  (vl-remove-illegitimate-tnames (cdr x) state))
       ((when car-legitp)
        (mv (cons (vl-tname-fix (car x)) cdr-prime) state)))
    (mv cdr-prime state)))

(define vl-scan-for-tnames-in-base-aux ((base   stringp)
                                        (models string-listp))
  :returns (tnames vl-tnamelist-p)
  :parents (vl-scan-for-tnames-in-base)
  :short "Convert the directory listing into a list of tnames."
  (if (atom models)
      nil
    (cons (make-vl-tname :base base :model (car models))
          (vl-scan-for-tnames-in-base-aux base (cdr models)))))

(define vl-scan-for-tnames-in-base ((base stringp)
                                    (state))
  :returns (mv (tnames vl-tnamelist-p)
               (state state-p1 :hyp (force (state-p1 state))))
  (b* ((dir (str::cat *vls-root* "/" base))
       ((mv err models state)
        (oslib::ls-subdirs dir))
       ((when err)
        (raise "Error listing directory ~x0: ~@1~%" dir err)
        (mv nil state)))
    (mv (vl-scan-for-tnames-in-base-aux base models)
        state))
  ///
  (more-returns
   (tnames true-listp :rule-classes :type-prescription)))

(define vl-scan-for-tnames-aux ((bases string-listp)
                                (state))
  :returns (mv (tnames vl-tnamelist-p)
               (state  state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom bases))
        (mv nil state))
       ((mv list1 state) (vl-scan-for-tnames-in-base (car bases) state))
       ((mv list2 state) (vl-scan-for-tnames-aux (cdr bases) state)))
    (mv (append list1 list2) state))
  ///
  (more-returns
   (tnames true-listp :rule-classes :type-prescription)))

(define vl-remove-temp-bases ((x string-listp))
  :returns (new-x string-listp)
  (cond ((atom x)
         nil)
        ((str::strprefixp "_temp_" (car x))
         (vl-remove-temp-bases (cdr x)))
        (t
         (cons (string-fix (car x))
               (vl-remove-temp-bases (cdr x))))))

(define vl-scan-for-tnames (state)
  :short "Top-level function for scanning for translation names."
  :returns (mv (tnames vl-tnamelist-p
                       "Names of all discovered, legitimate translations, with
                        no temporary translations.")
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((mv err val state)
        (oslib::ls-subdirs *vls-root*))
       ((when err)
        (raise "Error listing ~x0: ~x1." *vls-root* err)
        (mv nil state))
       (bases (vl-remove-temp-bases val))
       ((mv xlist state) (vl-scan-for-tnames-aux bases state))
       ((mv xlist state) (vl-remove-illegitimate-tnames xlist state)))
    (mv xlist state)))


(define vl-tnames-to-json-aux ((bases string-listp)
                               (x     vl-tnamelist-p))
  (b* (((when (atom bases))
        nil)
       (base1   (car bases))
       (tnames1 (vl-tnames-for-base base1 x))
       (models1 (vl-tnamelist-models tnames1)))
    (cons (cons base1 models1)
          (vl-tnames-to-json-aux (cdr bases) x))))

(define vl-tnames-to-json ((x vl-tnamelist-p))
  (b* ((bases (vls-sort-bases (vl-tnamelist-bases x))))
    (vl-tnames-to-json-aux bases x)))
