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
(include-book "fmt")
(include-book "find")
(include-book "centaur/bridge/to-json" :dir :system)
(local (include-book "../util/arithmetic"))


(defsection json-printing
  :parents (printer)
  :short "Routines for encoding various ACL2 structures into <a
href='http://www.json.org/'>JSON</a> format."

  :long "<p>This is a collection of printing routines for translating ACL2
structures into JSON format.  These routines are mainly meant to make it easy
to convert @(see vl) @(see syntax) into nice JSON data, but are somewhat
flexible and may be useful for other applications.</p>")


(defsection json-encoders
  :parents (json-printing)
  :short "A table of JSON encoders to use for for different kinds of data."
  :long "<p>A JSON encoder is a function of the following signature:</p>

@({ encode-foo : foo * ps --> ps })

<p>Where @('foo') is expected to be an object of some type @('foop'), and
@('ps') is the @(see vl) @(see printer) state stobj, @(see ps).  Each such
routine is responsible for printing a JSON encoding of its @('foop') argument.
Each such function may assume that @(see ps) is set to text mode.</p>

<p>The encoder table is a simple association of @('foop') to @('encode-foo')
functions.  We can use it to automatically generate encoders for, e.g., @(see
defaggregate) structures.</p>"

  (table vl-json)
  (table vl-json 'encoders
         ;; Alist binding each recognizer foop to its JSON encoder, vl-jp-foo
         )

  (defun get-json-encoders (world)
    "Look up the current alist of json encoders."
    (declare (xargs :mode :program))
    (cdr (assoc 'encoders (table-alist 'vl-json world))))

  (defmacro add-json-encoder (foop encoder-fn)
    (declare (xargs :guard (and (symbolp foop)
                                (symbolp encoder-fn))))
    `(table vl-json 'encoders
            (cons (cons ',foop ',encoder-fn)
                  (get-json-encoders world))))

  (defun get-json-encoder (foop world)
    (declare (xargs :mode :program))
    (let ((entry (assoc foop (get-json-encoders world))))
      (if entry
          (cdr entry)
        (er hard? 'get-json-encoder
            "No json encoder defined for ~x0.~%" foop)))))


#||
(get-json-encoders (w state))
(add-json-encoder barp vl-enc-bar)
(get-json-encoders (w state))
(get-json-encoder 'barp (w state)) ;; vl-enc-bar
(get-json-encoder 'foop (w state)) ;; fail, no encoder defined
||#


(define jp-bool ((x booleanp) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see booleanp) into JSON as @('true') or @('false')."
  (if x
      (vl-print-str "true")
    (vl-print-str "false")))

(add-json-encoder booleanp jp-bool)
(add-json-encoder not jp-bool)

(define jp-null (&key (ps 'ps))
  (vl-print "null"))

(define jp-col-after-printing-string-aux
  ((col natp    "Current column we're at.")
   (x   stringp "String we're about to print, not yet reversed.")
   (n   natp    "Current position in X.")
   (xl  natp    "Pre-computed length of X."))
  :returns (new-col natp :rule-classes :type-prescription)
  :parents (jp-str)
  :short "Fast way to figure out the new column after printing a JSON string
with proper encoding."
  :guard (and (<= n xl)
              (= xl (length x)))
  :measure (nfix (- (nfix xl) (nfix n)))
  (declare (type (integer 0 *) col n xl)
           (type string x))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (= n xl)))
        (lnfix col))
       ((the (unsigned-byte 8) code) (char-code (char x n)))
       ((when (or (<= code 31)
                  (>= code 127)))
        ;; This is a "json weird char."  Our encoder will turn it into
        ;; \uXXXX.  The length of \uXXXX is 6.
        (jp-col-after-printing-string-aux (+ 6 col) x (+ 1 (lnfix n)) xl)))
    ;; Else there is only one character.
    (jp-col-after-printing-string-aux (+ 1 col) x (+ 1 (lnfix n)) xl)))

(define jp-str ((x :type string) &key (ps 'ps))
  :parents (json-encoders)
  :short "Print the JSON encoding of a string, handling all escaping correctly
and including the surrounding quotes."
  :long "<p>We go to some effort to make this fast.</p>"
  (b* ((rchars  (vl-ps->rchars))
       (col     (vl-ps->col))
       (xl      (length x))
       (rchars  (cons #\" (bridge::json-encode-str-aux x 0 xl (cons #\" rchars))))
       (col     (+ 2 (jp-col-after-printing-string-aux col x 0 xl))))
    (vl-ps-seq
     (vl-ps-update-rchars rchars)
     (vl-ps-update-col col)))
  :prepwork
  ((local (defthm l0
            (implies (and (vl-printedlist-p acc)
                          (character-listp x))
                     (vl-printedlist-p (bridge::json-encode-chars x acc)))
            :hints(("Goal"
                    :in-theory (e/d (bridge::json-encode-chars
                                     bridge::json-encode-char
                                     bridge::json-encode-weird-char)
                                    (digit-to-char))))))))

(add-json-encoder stringp jp-str)

(define jp-maybe-string ((x maybe-stringp) &key (ps 'ps))
  :parents (json-encoders)
  (if x
      (jp-str x)
    (jp-null)))

(add-json-encoder maybe-stringp jp-maybe-string)

(define jp-maybe-string-list-aux ((x vl-maybe-string-list-p) &key (ps 'ps))
  (if (atom x) ps
    (vl-ps-seq (jp-maybe-string (first x))
               (if (atom (cdr x)) ps
                 (vl-println? ","))
               (jp-maybe-string-list-aux (rest x)))))

(define jp-maybe-string-list ((x vl-maybe-string-list-p) &key (ps 'ps))
  (vl-ps-seq (vl-print "[")
             (jp-maybe-string-list-aux x)
             (vl-print "]")))

(add-json-encoder vl-maybe-string-list-p jp-maybe-string-list)


(define jp-bignat ((x natp) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a potentially large natural number as a JSON string."
  (vl-print-str (str::natstr x)))

(define jp-nat ((x natp) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a probably small natural number as a JSON number."
  :long "<p>We require that the integer is at most 2^31, which we think is the
minimum reasonable size for a JSON implementation to support.</p>"
  (b* (((unless (<= x (expt 2 31)))
        (raise "Scarily trying to JSON-encode large natural: ~x0." x)
        ps))
    (vl-print-nat x)))

(define jp-maybe-nat ((x maybe-natp) &key (ps 'ps))
  :parents (json-encoders)
  (if x
      (jp-nat x)
    (jp-null)))

(add-json-encoder natp jp-nat)
(add-json-encoder posp jp-nat)
(add-json-encoder maybe-natp jp-maybe-nat)
(add-json-encoder maybe-posp jp-maybe-nat)



(define jp-sym-main ((x symbolp) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a simple symbol as a JSON string, including the surrounding
quotes."

  :long "<p>We assume that @('x') has a simple enough name to print without any
encoding.  This is generally true for keyword constants used as tags and in
basic enumerations like @(see vl-exprsign-p).  We print only the symbol name,
in lower-case.</p>"

  (vl-ps-seq (vl-print "\"")
             (vl-print-str (str::downcase-string (symbol-name x)))
             (vl-print "\"")))

(defsection jp-sym
  :parents (json-encoders)
  :short "Optimized version of @(see jp-sym-main)."
  :long "<p>This is a simple macro that is meant to be the same as @(see
jp-sym-main).  The only difference is that if we are given a literal symbol,
e.g., @(':foo'), we can do the string manipulation at compile time.</p>"

  (defmacro jp-sym (x &key (ps 'ps))
    (if (or (keywordp x)
            (booleanp x)
            (and (quotep x)
                 (symbolp (acl2::unquote x))))
        ;; Yes, want to optimize.
        (let* ((guts (if (quotep x) (acl2::unquote x) x))
               (ans  (str::cat "\""
                               (str::downcase-string (symbol-name guts))
                              "\"")))
          `(vl-print-str ,ans :ps ,ps))
      `(jp-sym-main ,x :ps ,ps))))

#||
(top-level (vl-cw-ps-seq (jp-sym :foo))) ;; "foo"
(top-level (vl-cw-ps-seq (jp-sym t)))    ;; "t"
(top-level (vl-cw-ps-seq (jp-sym nil)))  ;; "nil"
(top-level (vl-cw-ps-seq (jp-sym 'bar))) ;; "bar"
(top-level (let ((x 'baz))
             (vl-cw-ps-seq (jp-sym x)))) ;; "baz"
||#



(defsection jp-object
  :parents (json-encoders)
  :short "Utility for printing JSON <i>objects</i>, which in some other
languages might be called alists, dictionaries, hashes, records, etc."
  :long "<p>Syntax Example:</p>

@({
  (jp-object :tag  (vl-print \"loc\")
             :file (vl-print x.filename)
             :line (vl-print x.line)
             :col  (vl-print x.col))
   --->
  { \"tag\": \"loc\", \"file\": ... }
})

<p>The arguments to @('jp-object') should be an alternating list of literal
keywords, which (for better performance) we assume are so simple they do not
need to be encoded, and printing expressions which should handle any necessary
encoding.</p>"

  :autodoc nil

  (defun jp-object-aux (forms)
    (declare (xargs :guard t))
    (b* (((when (atom forms))
          nil)
         ((unless (keywordp (car forms)))
          (er hard? 'jp-object "Expected alternating keywords and values."))
         ((unless (consp (cdr forms)))
          (er hard? 'jp-object "No argument found after ~x0." (car forms)))
         ;; Suppose the keyword is :foo.
         ;; We create the string: "foo":
         ;; We can create this at macroexpansion time.
         (name1       (str::downcase-string (symbol-name (car forms))))
         (name1-colon (str::cat "\"" name1 "\": ")))
      (list* `(vl-print-str ,name1-colon)
;             (cond ((stringp (second forms))
;                    `(jp-str ,(second forms)))
                   ; ((symbolp (second forms))
                   ;  `(vl-print-str (symbol-name ,(second forms))))
;                   (t (second forms)))
             (second forms)
             (if (atom (cddr forms))
                 nil
               (cons `(vl-println? ", ")
                     (jp-object-aux (cddr forms)))))))

  (defmacro jp-object (&rest forms)
    `(vl-ps-seq (vl-print "{")
                ,@(jp-object-aux forms)
                (vl-println? "}"))))


(defmacro def-vl-jp-list (type &key
                               list-p
                               newlines)
  (declare (xargs :guard (maybe-natp newlines)))
  (b* ((mksym-package-symbol 'vl::foo)
       (list-p         (or list-p
                           (mksym 'vl- type 'list-p)))
       (elem-print     (mksym 'vl-jp- type))
       (list-print-aux (mksym 'vl-jp- type 'list-aux))
       (list-print     (mksym 'vl-jp- type 'list))
       (list-p-str     (symbol-name list-p)))
    `(encapsulate ()
       (define ,list-print-aux ((x ,list-p) &key (ps 'ps))
         :parents (,list-print)
         :short ,(cat "Prints out the elements of a @(see " list-p-str
                      ") without the enclosing brackets.")
         (if (atom x)
             ps
           (vl-ps-seq (,elem-print (car x))
                      (if (atom (cdr x))
                          ps
                        ,(if newlines
                             `(vl-ps-seq (vl-println ",")
                                         (vl-indent ,newlines))
                           `(vl-println? ", ")))
                      (,list-print-aux (cdr x)))))
       (define ,list-print ((x ,list-p) &key (ps 'ps))
         :parents (json-encoders)
         :short ,(cat "Prints out the elements of a @(see " list-p-str
                      ") with the enclosing brackets.")
         (vl-ps-seq (vl-print "[")
                    (,list-print-aux x)
                    (vl-println? "]")))
       (add-json-encoder ,list-p ,list-print))))

(define vl-jp-warning ((x vl-warning-p)
                       &key
                       (no-html)
                       (ps 'ps))
  :parents (json-encoders)
  :short "Special, custom JSON encoder for warnings."

  :long "<p>We probably don't want to use the ordinary aggregate-encoding stuff
to print @(see vl-warning-p) objects, since the types in the @(':args') field
are dynamic and, besides, who wants to reimplement @(see vl-cw) in other
languages.  Instead, it's probably more convenient to just go ahead and convert
the warning into a printed message here.  We'll include both HTML and plain
TEXT versions of the message.</p>"

  (b* (((vl-warning x) x)
       (text (with-local-ps
               ;; Historically, we used the default auto-wrap here.  But this
               ;; often results in long Verilog expressions getting
               ;; word-wrapped (1) by their author, and (2) by us after the
               ;; fact.  This often results in unfortunate formatting.  So now
               ;; we bump this up to a pretty large wrap, deferring to the
               ;; user's formatting unless they have really gone off the ranch.
               (vl-ps-update-autowrap-col 1000)
               (if x.context
                   (vl-cw-obj "~a0: ~@1" (list x.context (vl-msg x.msg x.args)))
                 (vl-cw-obj x.msg x.args))))
       ((when no-html)
        ;; Suppressing HTML output can be useful for reducing file sizes of
        ;; vl-warnings.json in VL Lint.
        (jp-object :tag    (vl-print "\"warning\"")
                   :fatalp (jp-bool x.fatalp)
                   :type   (jp-str (symbol-name x.type))
                   :fn     (jp-str (symbol-name x.fn))
                   :text   (jp-str text)))
       ;; Including HTML output can be useful for the module browser.
       (html (with-local-ps
               (vl-ps-update-htmlp t)
               ;; For the module browser, the warnings get word wrapped by the
               ;; browser anyway, so don't try to wrap them ourselves or things
               ;; get weird looking.
               (vl-ps-update-autowrap-col 100000)
               (if x.context
                   (vl-cw-obj "~a0: ~@1" (list x.context (vl-msg x.msg x.args)))
                 (vl-cw-obj x.msg x.args)))))
    (jp-object :tag    (vl-print "\"warning\"")
               :fatalp (jp-bool x.fatalp)
               :type   (jp-str (symbol-name x.type))
               :fn     (jp-str (symbol-name x.fn))
               :text   (jp-str text)
               :html   (jp-str html))))

(add-json-encoder vl-warning-p jp-warning)

(define vl-jp-warninglist-aux ((x vl-warninglist-p) &key no-html (ps 'ps))
  :parents (vl-jp-warninglist)
  :short "Prints out the elements of a @(see vl-warninglist-p) without the enclosing brackets."
         (if (atom x)
             ps
           (vl-ps-seq (vl-jp-warning (car x) :no-html no-html)
                      (if (atom (cdr x))
                          ps
                        (vl-ps-seq (vl-println ",")
                                   (vl-indent 4)))
                      (vl-jp-warninglist-aux (cdr x) :no-html no-html))))

(define vl-jp-warninglist ((x vl-warninglist-p) &key no-html (ps 'ps))
  :parents (json-encoders)
  :short "Prints out the elements of a @(see vl-warninglist-p) with the enclosing brackets."
  (vl-ps-seq (vl-print "[")
             (vl-jp-warninglist-aux x :no-html no-html)
             (vl-println? "]")))

(add-json-encoder vl-warninglist-p vl-jp-warninglist)


; Fancy automatic json encoding of std structures

(program)

(define make-json-encoder-alist
  (efields   ;; A proper std::formallist-p for this structure's fields
   omit      ;; A list of any fields to omit from the encoded output
   overrides ;; An alist of (fieldname . encoder-to-use-instead-of-default)
   world     ;; For looking up default encoders
   )
  ;; Returns an alist of the form (fieldname . encoder-to-use)
  (b* (((when (atom efields))
        nil)
       ((std::formal e1) (car efields))
       (- (cw "Determining encoder for ~x0... " e1.name))

       ;; Are we supposed to omit it?
       ((when (member e1.name omit))
        (cw "omitting it.~%")
        (make-json-encoder-alist (cdr efields) omit overrides world))

       ;; Are we supposed to override it?
       (look (assoc e1.name overrides))
       ((when look)
        (cw "overriding with ~x0.~%" (cdr look))
        (cons (cons e1.name (cdr look))
              (make-json-encoder-alist (cdr efields) omit overrides world)))

       ((unless (and (tuplep 2 e1.guard)
                     (equal (second e1.guard) e1.name)))
        (raise "Guard ~x0 too complex.~%" e1.guard))

       (predicate (first e1.guard))
       (encoder   (get-json-encoder predicate world)))
    (cw "defaulting to ~x0~%" encoder)
    (cons (cons e1.name encoder)
          (make-json-encoder-alist (cdr efields) omit overrides world))))

(define encoder-alist-main-actions
  (basename ;; base name for aggregate, e.g., 'vl-location
   alist    ;; alist of fields->encoder to use
   newlines ;; NIL means don't auto-newline between elements; any number means
            ;; newline and indent to that many places between lines
   )
  (b* (((when (atom alist))
        nil)
       ((cons fieldname encoder) (car alist))
       (foo->bar                 (std::da-accessor-name basename fieldname))
       ;; Suppose the fieldname is foo.  We create the string ["foo":].  We can
       ;; create this at macroexpansion time.
       (name1       (str::downcase-string (symbol-name fieldname)))
       (name1-colon (str::cat "\"" name1 "\": ")))
    (list* `(vl-print-str ,name1-colon)
           `(,encoder (,foo->bar x))
           (if (atom (cdr alist))
               nil
             (cons (if newlines
                       `(vl-ps-seq (vl-println ", ")
                                   (vl-indent ,newlines))
                     `(vl-println? ", "))
                   (encoder-alist-main-actions basename (cdr alist) newlines))))))


(define convert-flexprod-fields-into-eformals ((x "list of fty::flexprod-fields"))
  (b* (((when (atom x))
        nil)
       ((fty::flexprod-field x1) (car x)))
    (cons (std::make-formal :name x1.name
                            :guard (list x1.type x1.name))
          (convert-flexprod-fields-into-eformals (cdr x)))))

#|

(define def-vl-jp-prod-fn (prod omit )

  (vl-ps-seq
        (vl-print "{\"tag\": ")
        (jp-sym ',tag)
        ,(if newlines
             `(vl-ps-seq (vl-println ", ")
                         (vl-indent ,newlines))
           `(vl-print ", "))
        ,@main
        (vl-println? "}"))

             (suminfo (fty::get-flexsum-info elem world))
             ((unless suminfo)
              (mv (raise "Type ~x0 doesn't look like a known defaggregate/defprod?~%" type)
                  nil))
             ((fty::suminfo suminfo))

             (prod (car (fty::flexsum->prods suminfo.sum)))
             (efields (convert-flexprod-fields-into-eformals
                       (fty::flexprod->fields prod)))
             (tag (car (fty::suminfo->tags suminfo))))

|#

(define def-vl-jp-aggregate-fn (type omit overrides long newlines world)
  (b* ((mksym-package-symbol 'vl::foo)
       (elem-print     (mksym 'vl-jp- type))
       (elem           (mksym 'vl- type))
       (elem-p         (mksym 'vl- type '-p))
       (elem-p-str     (symbol-name elem-p))

       ((mv tag efields)
        (b* ((agginfo (std::get-aggregate elem world))
             ((when agginfo)
              (cw "Found info for defaggregate ~x0.~%" type)
              (mv (std::agginfo->tag agginfo)
                  (std::agginfo->efields agginfo)))
             ((mv & type) (fty::search-deftypes-table elem (fty::get-flextypes world)))
             ((unless (and type
                           (equal (tag type) :sum)
                           (equal (len (fty::flexsum->prods type)) 1)))
              (mv (raise "Type ~x0 doesn't look like a known defaggregate/defprod?~%" type)
                  nil))
             (prod    (car (fty::flexsum->prods type)))
             (efields (convert-flexprod-fields-into-eformals (fty::flexprod->fields prod)))
             (tag     (fty::flexprod->kind prod)))
          (mv tag efields)))

       (- (cw "Inferred tag ~x0.~%" tag))
       (- (cw "Inferred fields ~x0.~%" efields))

       ((unless (std::formallist-p efields))
        (raise "Expected :efields for ~x0 to be a valid formallist, found ~x1."
               elem efields))
       (enc-alist (make-json-encoder-alist efields omit overrides world))
       ((unless (consp enc-alist))
        (raise "Expected at least one field to encode."))
       (main      (encoder-alist-main-actions elem enc-alist newlines)))

    `(define ,elem-print ((x ,elem-p) &key (ps 'ps))
       :parents (json-encoders)
       :short ,(cat "Print the JSON encoding of a @(see " elem-p-str
                    ") to @(see ps).")
       :long ,long
       (vl-ps-seq
        (vl-print "{\"tag\": ")
        (jp-sym ',tag)
        ,(if newlines
             `(vl-ps-seq (vl-println ", ")
                         (vl-indent ,newlines))
           `(vl-print ", "))
        ,@main
        (vl-println? "}"))
       ///
       (add-json-encoder ,elem-p ,elem-print))))

#|
(def-vl-jp-aggregate-fn
  'location
  '(col)
  '((filename . blah))
  "long"
  (w state))
|#

(defmacro def-vl-jp-aggregate (type &key omit override newlines
                                    (long '""))
  (declare (xargs :guard (maybe-natp newlines)))
  `(make-event
    (let ((form (def-vl-jp-aggregate-fn ',type ',omit ',override ',long ',newlines
                  (w state))))
      (value form))))

(defmacro def-vl-jp-option (type &key
                                 option-p)
  (b* ((mksym-package-symbol 'vl::foo)
       (option-p       (or option-p
                           (mksym 'vl-maybe- type '-p)))
       (elem-print     (mksym 'vl-jp- type))
       (opt-print      (mksym 'vl-jp-maybe- type))
       (opt-p-str      (symbol-name option-p)))
    `(encapsulate ()
       (define ,opt-print ((x ,option-p) &key (ps 'ps))
         :parents (json-encoders)
         :short ,(cat "Prints out optional @(see " opt-p-str
                      ") as either null or type.")
         (if x (,elem-print x) (jp-null)))
       (add-json-encoder ,option-p ,opt-print))))

(logic)






;; Real Verilog JSON Encoding

(define vl-jp-exprsign ((x vl-exprsign-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-cstrength ((x vl-cstrength-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-dstrength ((x vl-dstrength-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-direction ((x vl-direction-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-gatetype ((x vl-gatetype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-evatomtype ((x vl-evatomtype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-assign-type ((x vl-assign-type-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-deassign-type ((x vl-deassign-type-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-casecheck ((x vl-casecheck-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-casetype ((x vl-casetype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-casekey ((x vl-casekey-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-alwaystype ((x vl-alwaystype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(add-json-encoder vl-exprsign-p         vl-jp-exprsign)
(add-json-encoder vl-cstrength-p        vl-jp-cstrength)
(add-json-encoder vl-dstrength-p        vl-jp-dstrength)
(add-json-encoder vl-direction-p        vl-jp-direction)
(add-json-encoder vl-gatetype-p         vl-jp-gatetype)
(add-json-encoder vl-evatomtype-p       vl-jp-evatomtype)
(add-json-encoder vl-assign-type-p      vl-jp-assign-type)
(add-json-encoder vl-deassign-type-p    vl-jp-deassign-type)
(add-json-encoder vl-casetype-p         vl-jp-casetype)
(add-json-encoder vl-casecheck-p        vl-jp-casecheck)
(add-json-encoder vl-casekey-p          vl-jp-casekey)
(add-json-encoder vl-alwaystype-p       vl-jp-alwaystype)


(define vl-jp-maybe-exprsign ((x vl-maybe-exprsign-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (if x
      (vl-jp-exprsign x)
    (jp-null)))

(define vl-jp-maybe-cstrength ((x vl-maybe-cstrength-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (if x
      (vl-jp-cstrength x)
    (jp-null)))

(define vl-jp-maybe-direction ((x vl-maybe-direction-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (if x
      (vl-jp-direction x)
    (jp-null)))

(add-json-encoder vl-maybe-exprsign-p  vl-jp-maybe-exprsign)
(add-json-encoder vl-maybe-cstrength-p vl-jp-maybe-cstrength)
(add-json-encoder vl-maybe-direction-p vl-jp-maybe-direction)

(define vl-jp-location ((x vl-location-p) &key (ps 'ps))
  (jp-str (vl-location-string x)))

(add-json-encoder vl-location-p vl-jp-location)

#||
(top-level
 (vl-cw-ps-seq (vl-jp-location *vl-fakeloc*)))
||#


(define jp-bit ((x vl-bit-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see vl-bit-p) as a JSON string."
  (jp-str (implode (list (vl-bit->char x)))))

(add-json-encoder vl-bit-p jp-bit)

(define jp-bitlist ((x vl-bitlist-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see vl-bitlist-p) as a JSON string."
  (jp-str (vl-bitlist->string x)))

(add-json-encoder vl-bitlist-p jp-bitlist)

(define jp-timeunit ((x vl-timeunit-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see vl-timeunit-p) as a JSON string."
  (jp-str (vl-timeunit->string x)))

(add-json-encoder vl-timeunit-p jp-timeunit)

;;;;

(define vl-jp-constint ((x vl-value-p) &key (ps 'ps))
  :guard (equal (vl-value-kind x) :vl-constint)
  :parents (json-encoders)
  :long "<p>Note that we always encode the value as a string.  This is
because it is quite common for Verilog constants to run into the hundreds
of bits, but the JSON standard doesn't really ever say how big of numbers
must be supported and JSON implementations often use machine integers
which could not hold such large values.</p>"
  (jp-object :tag (jp-sym (vl-value-kind x))
             :origwidth (jp-nat (vl-constint->origwidth x))
             :value (jp-bignat (vl-constint->value x))
             :origsign (jp-str (symbol-name (vl-constint->origsign x)))
             :wasunsized (jp-bool (vl-constint->wasunsized x))))

(define vl-jp-weirdint ((x vl-value-p) &key (ps 'ps))
  :guard (equal (vl-value-kind x) :vl-weirdint)
  :parents (json-encoders)
  (jp-object :tag (jp-sym (vl-value-kind x))
             :bits (jp-bitlist (vl-weirdint->bits x))
             :origsign (jp-str (symbol-name (vl-weirdint->origsign x)))
             :wasunsized (jp-bool (vl-weirdint->wasunsized x))))

(define vl-jp-extint ((x vl-value-p) &key (ps 'ps))
  :guard (equal (vl-value-kind x) :vl-extint)
  :parents (json-encoders)
  (jp-object :tag (jp-sym (vl-value-kind x))
             :value (jp-bit (vl-extint->value x))))

(define vl-jp-string ((x vl-value-p) &key (ps 'ps))
  :guard (equal (vl-value-kind x) :vl-string)
  :parents (json-encoders)
  (jp-object :tag (jp-sym (vl-value-kind x))
             :value (jp-str (vl-string->value x))))

(define vl-jp-real ((x vl-value-p) &key (ps 'ps))
  :guard (equal (vl-value-kind x) :vl-real)
  :parents (json-encoders)
  (jp-object :tag (jp-sym (vl-value-kind x))
             :value (jp-str (vl-real->value x))))

(define vl-jp-time ((x vl-value-p) &key (ps 'ps))
  :guard (equal (vl-value-kind x) :vl-time)
  :parents (json-encoders)
  (jp-object :tag (jp-sym (vl-value-kind x))
             :quantity (jp-str (vl-time->quantity x))
             :units (jp-str (symbol-name (vl-time->units x)))))

(define vl-jp-value ((x vl-value-p) &key (ps 'ps))
  :parents (json-encoders)
  (vl-value-case x
    :vl-constint (vl-jp-constint x)
    :vl-weirdint (vl-jp-weirdint x)
    :vl-extint   (vl-jp-extint x)
    :vl-string   (vl-jp-string x)
    :vl-real     (vl-jp-real x)
    :vl-time     (vl-jp-time x)))

(add-json-encoder vl-value-p vl-jp-value)

;;;;;;;;

(define jp-ssn (x &key (ps 'ps))
  :guard (or (stringp x) (symbolp x) (acl2-numberp x))
  (cond ((symbolp x) (jp-sym x))
        ((stringp x) (jp-str x))
        (t (vl-print x)))) ;; BOZO -- I think numbers can just be printed?

;;;;;;; begin big vl-expr mutual-recursion and encoders..

;; under vl-expr tagsum:

(defabbrev vl-jp-index (x y.kind)
  (b* (((vl-index y) x))
    (jp-object :tag (jp-sym y.kind)
               :scope (vl-jp-scopeexpr y.scope)
               :indices (vl-jp-exprlist y.indices)
               :part (vl-jp-partselect y.part)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-unary (x y.kind)
  (b* (((vl-unary y) x))
    (jp-object :tag (jp-sym y.kind)
               :op (jp-ssn y.op)
               :arg (vl-jp-expr y.arg)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-binary (x y.kind)
  (b* (((vl-binary y) x))
    (jp-object :tag (jp-sym y.kind)
               :op (jp-ssn y.op)
               :left (vl-jp-expr y.left)
               :right (vl-jp-expr y.right)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-qmark (x y.kind)
  (b* (((vl-qmark y) x))
    (jp-object :tag (jp-sym y.kind)
               :test (vl-jp-expr y.test)
               :then (vl-jp-expr y.then)
               :else (vl-jp-expr y.else)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-concat (x y.kind)
  (b* (((vl-concat y) x))
    (jp-object :tag (jp-sym y.kind)
               :parts (vl-jp-exprlist y.parts)
               :atts  (vl-jp-atts y.atts))))

(defabbrev vl-jp-multiconcat (x y.kind)
  (b* (((vl-multiconcat y) x))
    (jp-object :tag (jp-sym y.kind)
               :reps  (vl-jp-expr y.reps)
               :parts (vl-jp-exprlist y.parts)
               :atts  (vl-jp-atts y.atts))))

(defabbrev vl-jp-mintypmax (x y.kind)
  (b* (((vl-mintypmax y) x))
    (jp-object :tag (jp-sym y.kind)
               :min (vl-jp-expr y.min)
               :typ (vl-jp-expr y.typ)
               :max (vl-jp-expr y.max))))

(defabbrev vl-jp-call (x y.kind)
  (b* (((vl-call y) x))
    (jp-object :tag (jp-sym y.kind)
               :name (vl-jp-scopeexpr y.name)
               :plainargs (vl-jp-maybe-exprlist y.plainargs)
               :namedargs (vl-jp-call-namedargs y.namedargs)
               :typearg (vl-jp-maybe-datatype y.typearg)
               :systemp (jp-bool y.systemp)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-stream (x y.kind)
  (b* (((vl-stream y) x))
    (jp-object :tag (jp-sym y.kind)
               :dir (jp-ssn y.dir)
               :size (vl-jp-slicesize y.size)
               :parts (vl-jp-streamexprlist y.parts)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-cast (x y.kind)
  (b* (((vl-cast y) x))
    (jp-object :tag (jp-sym y.kind)
               :to (vl-jp-casttype y.to)
               :expr (vl-jp-expr y.expr)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-inside (x y.kind)
  (b* (((vl-inside y) x))
    (jp-object :tag (jp-sym y.kind)
               :elem (vl-jp-expr y.elem)
               :set (vl-jp-valuerangelist y.set)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-tagged (x y.kind)
  (b* (((vl-tagged y) x))
    (jp-object :tag (jp-sym y.kind)
               :name (jp-ssn y.tag)
               :expr (vl-jp-maybe-expr y.expr)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-pattern (x y.kind)
  (b* (((vl-pattern y) x))
    (jp-object :tag (jp-sym y.kind)
               :pat (vl-jp-assignpat y.pat)
               :pattype (vl-jp-maybe-datatype y.pattype)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-special (x y.kind)
  (b* (((vl-special y) x))
    (jp-object :tag (jp-sym y.kind)
               :key (jp-ssn y.key)
               :atts (vl-jp-atts y.atts))))

(defabbrev vl-jp-eventexpr (x y.kind)
  (b* (((vl-eventexpr y) x))
    (jp-object :tag (jp-sym y.kind)
               :atoms (vl-jp-evatomlist y.atoms)
               :atts (vl-jp-atts y.atts))))

;; under vl-dataype tagsum:

(defabbrev vl-jp-coretype (x y.kind)
  (b* (((vl-coretype y) x))
    (jp-object :tag (jp-sym y.kind)
               :name (jp-ssn y.name)
               :pdims (vl-jp-dimensionlist y.pdims)
               :udims (vl-jp-dimensionlist y.udims)
               :signed (jp-bool y.signedp))))

(defabbrev vl-jp-struct (x y.kind)
  (b* (((vl-struct y) x))
    (jp-object :tag (jp-sym y.kind)
               :members (vl-jp-structmemberlist y.members)
               :packed (jp-bool y.packedp)
               :pdims (vl-jp-dimensionlist y.pdims)
               :udims (vl-jp-dimensionlist y.udims)
               :signed (jp-bool y.signedp))))

(defabbrev vl-jp-union (x y.kind)
  (b* (((vl-union y) x))
    (jp-object :tag (jp-sym y.kind)
               :members (vl-jp-structmemberlist y.members)
               :packed (jp-bool y.packedp)
               :pdims (vl-jp-dimensionlist y.pdims)
               :udims (vl-jp-dimensionlist y.udims)
               :signed (jp-bool y.signedp)
               :tagged (jp-bool y.taggedp))))

(defabbrev vl-jp-enum (x y.kind)
  (b* (((vl-enum y) x))
    (jp-object :tag (jp-sym y.kind)
               :basetype (vl-jp-datatype y.basetype)
               :items (vl-jp-enumitemlist y.items)
               :values (vl-jp-exprlist y.values)
               :pdims (vl-jp-dimensionlist y.pdims)
               :udims (vl-jp-dimensionlist y.udims))))

(defabbrev vl-jp-usertype (x y.kind)
  (b* (((vl-usertype y) x))
    (jp-object :tag (jp-sym y.kind)
               :name (vl-jp-scopeexpr y.name)
               :res (vl-jp-maybe-datatype y.res)
               :pdims (vl-jp-dimensionlist y.pdims)
               :udims (vl-jp-dimensionlist y.udims))))

(local (defthm hidname-p-ssn-p
         (implies (and (vl-hidname-p x) (not (stringp x)))
                  (symbolp x))
         :hints (("Goal" :in-theory (enable vl-hidname-p)))))

(local (defthm scopename-p-ssn-p
         (implies (and (vl-scopename-p x) (not (stringp x)))
                  (symbolp x))
         :hints (("Goal" :in-theory (enable vl-scopename-p)))))

(defines vl-jp-expr
  :parents (json-encoders)

  (define vl-jp-expr ((x vl-expr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-expr-count x) 0)
    (vl-expr-case x
      :vl-literal     (vl-jp-value x.val)
      :vl-index       (vl-jp-index x x.kind)
      :vl-unary       (vl-jp-unary x x.kind)
      :vl-binary      (vl-jp-binary x x.kind)
      :vl-qmark       (vl-jp-qmark x x.kind)
      :vl-concat      (vl-jp-concat x x.kind)
      :vl-multiconcat (vl-jp-multiconcat x x.kind)
      :vl-mintypmax   (vl-jp-mintypmax x x.kind)
      :vl-call        (vl-jp-call x x.kind)
      :vl-stream      (vl-jp-stream x x.kind)
      :vl-cast        (vl-jp-cast x x.kind)
      :vl-inside      (vl-jp-inside x x.kind)
      :vl-tagged      (vl-jp-tagged x x.kind)
      :vl-pattern     (vl-jp-pattern x x.kind)
      :vl-special     (vl-jp-special x x.kind)
      :vl-eventexpr   (vl-jp-eventexpr x x.kind)))

  (define vl-jp-exprlist ((x vl-exprlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-exprlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-exprlist-aux x)
               (vl-println? "]")))

  (define vl-jp-exprlist-aux ((x vl-exprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-exprlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-expr (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-exprlist-aux (cdr x)))))

  (define vl-jp-maybe-expr ((x vl-maybe-expr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-maybe-expr-count x) 0)
    (if x (vl-jp-expr x) (jp-null)))

  (define vl-jp-maybe-exprlist ((x vl-maybe-exprlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-maybe-exprlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-maybe-exprlist-aux x)
               (vl-println? "]")))

  (define vl-jp-maybe-exprlist-aux ((x vl-maybe-exprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-maybe-exprlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-maybe-expr (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-maybe-exprlist-aux (cdr x)))))

  (define vl-jp-call-namedargs ((x vl-call-namedargs-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-call-namedargs-count x) 1)
    (vl-ps-seq (vl-print "{")
               (vl-jp-call-namedargs-aux x)
               (vl-println? "}")))

  (define vl-jp-call-namedargs-aux ((x vl-call-namedargs-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-call-namedargs-count x) 0)
    (b* (((when (atom x))
          ps)
         ((when (mbe :logic (not (vl-call-namedargs-p x)) :exec nil))
          ps))
      (vl-ps-seq (jp-str (caar x))
                 (vl-print ": ")
                 (vl-jp-maybe-expr (cdar x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-call-namedargs-aux (cdr x)))))
  
  (define vl-jp-atts ((x vl-atts-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-atts-count x) 1)
    ;; Atts are a string->maybe-expr alist, so turn them into a JSON object
    ;; binding keys to values...
    (vl-ps-seq (vl-print "{")
               (vl-jp-atts-aux x)
               (vl-println? "}")))

  (define vl-jp-atts-aux ((x vl-atts-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-atts-count x) 0)
    (b* ((x (vl-atts-fix x))
         ((when (atom x))
          ps)
         ((cons name1 val1) (car x)))
      (vl-ps-seq (jp-str name1)
                 (vl-print ": ")
                 (if val1
                     (vl-jp-maybe-expr val1)
                   (jp-null))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-atts-aux (cdr x)))))

  (define vl-jp-range ((x vl-range-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-range-count x) 0)
    (jp-object :tag (jp-sym :vl-range)
               :msb (vl-jp-expr (vl-range->msb x))
               :lsb (vl-jp-expr (vl-range->lsb x))))

  (define vl-jp-maybe-range ((x vl-maybe-range-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-maybe-range-count x) 0)
    (if x (vl-jp-range x) (jp-null)))

  (define vl-jp-dimension ((x vl-dimension-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-dimension-count x) 0)
    (vl-dimension-case x
       (:unsized  (jp-object :tag (jp-sym x.kind)))
       (:star     (jp-object :tag (jp-sym x.kind)))
       (:datatype (jp-object :tag (jp-sym x.kind)
                             :type (vl-jp-datatype
                                    (vl-dimension->type x))))
       (:queue    (jp-object :tag (jp-sym x.kind)
                             :maxsize (vl-jp-maybe-expr
                                       (vl-dimension->maxsize x))))
       (:range    (jp-object :tag (jp-sym x.kind)
                             :range (vl-jp-range
                                     (vl-dimension->range x))))))

  (define vl-jp-dimensionlist ((x vl-dimensionlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-dimensionlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-dimensionlist-aux x)
               (vl-println? "]")))

  (define vl-jp-dimensionlist-aux ((x vl-dimensionlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-dimensionlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-dimension (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-dimensionlist-aux (cdr x)))))

  (define vl-jp-maybe-dimension ((x vl-maybe-dimension-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-maybe-dimension-count x) 0)
    (if x (vl-jp-dimension x) (jp-null)))

  (define vl-jp-hidindex ((x vl-hidindex-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-hidindex-count x) 0)
    (jp-object :tag (jp-sym :vl-hidindex)
               :name (jp-ssn (vl-hidindex->name x))
               :indices (vl-jp-exprlist (vl-hidindex->indices x))))
  
  (define vl-jp-hidexpr ((x vl-hidexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-hidexpr-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-hidexpr-aux x)
               (vl-println? "]")))

  (define vl-jp-hidexpr-aux ((x vl-hidexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-hidexpr-count x) 0)
    (vl-hidexpr-case x
      (:end (jp-object :end (jp-str (vl-hidexpr-end->name x))))
      (:dot (vl-ps-seq (jp-object :dot (vl-jp-hidindex (vl-hidexpr-dot->first x)))
                       (vl-jp-hidexpr-aux (vl-hidexpr-dot->rest x))))))

  (define vl-jp-scopeexpr ((x vl-scopeexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-scopeexpr-count x) 0)
    (vl-scopeexpr-case x
      (:colon (jp-object :tag (jp-sym x.kind)
                         :first (jp-ssn          (vl-scopeexpr-colon->first x))
                         :rest  (vl-jp-scopeexpr (vl-scopeexpr-colon->rest x))))
      (:end   (vl-jp-hidexpr (vl-scopeexpr-end->hid x)))))

  (define vl-jp-plusminus ((x vl-plusminus-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-plusminus-count x) 0)
    (jp-object :base   (vl-jp-expr (vl-plusminus->base  x))
               :width  (vl-jp-expr (vl-plusminus->width x))
               :minusp (jp-bool (vl-plusminus->minusp x))))

  (define vl-jp-partselect ((x vl-partselect-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-partselect-count x) 0)
    (vl-partselect-case x
      (:none (jp-sym :none))
      (:range (jp-object :range (vl-jp-range (vl-partselect->range x))))
      (:plusminus (jp-object :plusminus (vl-jp-plusminus (vl-partselect->plusminus x))))))
  
  (define vl-jp-valuerange ((x vl-valuerange-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-valuerange-count x) 0)
    (vl-valuerange-case x
      (:valuerange-range  (jp-object :tag  (jp-sym x.kind)
                                     :low  (vl-jp-expr (vl-valuerange-range->low x))
                                     :high (vl-jp-expr (vl-valuerange-range->high x))))
      (:valuerange-single (jp-object :tag  (jp-sym x.kind)
                                     :expr (vl-jp-expr (vl-valuerange-single->expr x))))))

  (define vl-jp-valuerangelist ((x vl-valuerangelist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-valuerangelist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-valuerangelist-aux x)
               (vl-println? "]")))

  (define vl-jp-valuerangelist-aux ((x vl-valuerangelist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-valuerangelist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-valuerange (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-valuerangelist-aux (cdr x)))))

  (define vl-jp-slicesize ((x vl-slicesize-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-slicesize-count x) 0)
    (vl-slicesize-case x
      (:none ps) ;; print out nothing here?
      (:expr (jp-object :expr (vl-jp-expr (vl-slicesize-expr->expr x))))
      (:type (jp-object :type (vl-jp-datatype (vl-slicesize-type->type x))))))

  (define vl-jp-streamexpr ((x vl-streamexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-streamexpr-count x) 0)
    (jp-object :tag (jp-sym :vl-streamexpr)
               :expr (vl-jp-expr (vl-streamexpr->expr x))
               :part (vl-jp-arrayrange (vl-streamexpr->part x))))

  (define vl-jp-streamexprlist ((x vl-streamexprlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-streamexprlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-streamexprlist-aux x)
               (vl-println? "]")))

  (define vl-jp-streamexprlist-aux ((x vl-streamexprlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-streamexprlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-streamexpr (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-streamexprlist-aux (cdr x)))))

  (define vl-jp-arrayrange ((x vl-arrayrange-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-arrayrange-count x) 0)
    (vl-arrayrange-case x
      (:none ps) ;; print out nothing here?
      (:range (jp-object :range (vl-jp-range (vl-arrayrange->range x))))
      (:plusminus (jp-object :plusminus (vl-jp-plusminus (vl-arrayrange->plusminus x))))
      (:index (jp-object :index (vl-jp-expr (vl-arrayrange->expr x))))))

  (define vl-jp-casttype ((x vl-casttype-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-casttype-count x) 0)
    (vl-casttype-case x
      (:type (jp-object :type (vl-jp-datatype (vl-casttype-type->type x))))
      (:size (jp-object :size (vl-jp-expr (vl-casttype-size->size x))))
      (:signedness (jp-object :signedness (jp-bool (vl-casttype-signedness->signedp x))))
      (:const (jp-object :const (jp-bool t)))))

  (define vl-jp-patternkey ((x vl-patternkey-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-patternkey-count x) 0)
    (vl-patternkey-case x
      (:expr (jp-object :expr (vl-jp-expr (vl-patternkey-expr->key x))))
      (:structmem (jp-object :structmem (jp-str (vl-patternkey-structmem->name x))))
      (:type (jp-object :type (vl-jp-datatype (vl-patternkey-type->type x))))
      (:default (jp-str "default"))))

  (define vl-jp-keyvallist ((x vl-keyvallist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-keyvallist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-keyvallist-aux x)
               (vl-println? "]")))

  (define vl-jp-keyvallist-aux ((x vl-keyvallist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-keyvallist-count x) 0)
    (b* (((when (atom x))
          ps)
         ((when (mbe :logic (not (vl-keyvallist-p x)) :exec nil))
          ps))
      (vl-ps-seq (vl-print "[")
                 (vl-jp-patternkey (caar x))
                 (vl-print ",")
                 (vl-jp-expr (cdar x))
                 (vl-print "]")
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-keyvallist-aux (cdr x)))))

  (define vl-jp-assignpat ((x vl-assignpat-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-assignpat-count x) 0)
    (vl-assignpat-case x
      (:positional (jp-object :positional 
                              (vl-jp-exprlist (vl-assignpat-positional->vals x))))
      (:keyval (jp-object :keyval
                          (vl-jp-keyvallist (vl-assignpat-keyval->pairs x))))
      (:repeat (jp-object :repeat (jp-null)
                          :reps (vl-jp-expr (vl-assignpat-repeat->reps x))
                          :vals (vl-jp-exprlist (vl-assignpat-repeat->vals x))))))
                              
  (define vl-jp-datatype ((x vl-datatype-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-datatype-count x) 0)
    (vl-datatype-case x
      (:vl-coretype (vl-jp-coretype x x.kind))
      (:vl-struct   (vl-jp-struct x x.kind))
      (:vl-union    (vl-jp-union x x.kind))
      (:vl-enum     (vl-jp-enum x x.kind))
      (:vl-usertype (vl-jp-usertype x x.kind))))

  (define vl-jp-maybe-datatype ((x vl-maybe-datatype-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-maybe-datatype-count x) 0)
    (if x (vl-jp-datatype x) (jp-null)))

  (define vl-jp-structmember ((x vl-structmember-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-structmember-count x) 0)
    (jp-object :tag  (jp-sym :vl-structmember)
               :type (vl-jp-datatype (vl-structmember->type x))
               :name (jp-str (vl-structmember->name x))
               :rhs  (vl-jp-maybe-expr (vl-structmember->rhs x))
               :rand (jp-ssn (vl-structmember->rand x))
               :atts (vl-jp-atts (vl-structmember->atts x))))

  (define vl-jp-structmemberlist ((x vl-structmemberlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-structmemberlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-structmemberlist-aux x)
               (vl-println? "]")))

  (define vl-jp-structmemberlist-aux ((x vl-structmemberlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-structmemberlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-structmember (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-structmemberlist-aux (cdr x)))))

  (define vl-jp-enumitem ((x vl-enumitem-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-enumitem-count x) 0)
    (jp-object :tag  (jp-sym :vl-enumitem)
               :name (jp-str (vl-enumitem->name x))
               :range (vl-jp-maybe-range (vl-enumitem->range x))
               :value (vl-jp-maybe-expr (vl-enumitem->value x))))

  (define vl-jp-enumitemlist ((x vl-enumitemlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-enumitemlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-enumitemlist-aux x)
               (vl-println? "]")))

  (define vl-jp-enumitemlist-aux ((x vl-enumitemlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-enumitemlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-enumitem (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-enumitemlist-aux (cdr x)))))

  (define vl-jp-evatom ((x vl-evatom-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-evatom-count x) 0)
    (jp-object :tag  (jp-sym :vl-evatom)
               :type (vl-jp-evatomtype (vl-evatom->type x))
               :expr (vl-jp-expr (vl-evatom->expr x))))

  (define vl-jp-evatomlist ((x vl-evatomlist-p) &key (ps 'ps))
    ;; Print the expressions as a JSON array with brackets.
    :measure (two-nats-measure (vl-evatomlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-evatomlist-aux x)
               (vl-println? "]")))

  (define vl-jp-evatomlist-aux ((x vl-evatomlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-evatomlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-evatom (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-evatomlist-aux (cdr x)))))
) ;; end defines vl-jp-expr

(add-json-encoder vl-expr-p             vl-jp-expr)
(add-json-encoder vl-exprlist-p         vl-jp-exprlist)
(add-json-encoder vl-maybe-expr-p       vl-jp-maybe-expr)
(add-json-encoder vl-maybe-exprlist-p   vl-jp-maybe-exprlist)
(add-json-encoder vl-call-namedargs-p   vl-jp-call-namedargs)
(add-json-encoder vl-atts-p             vl-jp-atts)
(add-json-encoder vl-range-p            vl-jp-range)
(add-json-encoder vl-maybe-range-p      vl-jp-maybe-range)
(add-json-encoder vl-dimension-p        vl-jp-dimension)
(add-json-encoder vl-dimensionlist-p    vl-jp-dimensionlist)
(add-json-encoder vl-hidindex-p         vl-jp-hidindex)
(add-json-encoder vl-hidexpr-p          vl-jp-hidexpr)
(add-json-encoder vl-scopeexpr-p        vl-jp-scopeexpr)
(add-json-encoder vl-plusminus-p        vl-jp-plusminus)
(add-json-encoder vl-partselect-p       vl-jp-partselect)
(add-json-encoder vl-valuerange-p       vl-jp-valuerange)
(add-json-encoder vl-valuerangelist-p   vl-jp-valuerangelist)
(add-json-encoder vl-slicesize-p        vl-jp-slicesize)
(add-json-encoder vl-streamexpr-p       vl-jp-streamexpr)
(add-json-encoder vl-streamexprlist-p   vl-jp-streamexprlist)
(add-json-encoder vl-streamexpr-p       vl-jp-streamexpr)
(add-json-encoder vl-arrayrange-p       vl-jp-arrayrange)
(add-json-encoder vl-casttype-p         vl-jp-casttype)
(add-json-encoder vl-patternkey-p       vl-jp-patternkey)
(add-json-encoder vl-keyvallist-p       vl-jp-keyvallist)
(add-json-encoder vl-assignpat-p        vl-jp-assignpat)
(add-json-encoder vl-datatype-p         vl-jp-datatype)
(add-json-encoder vl-maybe-datatype-p   vl-jp-maybe-datatype)
(add-json-encoder vl-structmember-p     vl-jp-structmember)
(add-json-encoder vl-structmemberlist-p vl-jp-structmemberlist)
(add-json-encoder vl-enumitem-p         vl-jp-enumitem)
(add-json-encoder vl-enumitemlist-p     vl-jp-enumitemlist)
(add-json-encoder vl-evatom-p           vl-jp-evatom)
(add-json-encoder vl-evatomlist-p       vl-jp-evatomlist)

;;;;;;; end big vl-expr mutual-recursion and encoders..

;;;;;;; begin big vl-stmt mutual-recursion and encoders..

(def-vl-jp-aggregate delaycontrol)
(def-vl-jp-aggregate eventcontrol)
(def-vl-jp-aggregate repeateventcontrol)

(define vl-jp-delayoreventcontrol ((x vl-delayoreventcontrol-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-delayoreventcontrol-p)))
  (cond ((vl-delaycontrol-p x) (vl-jp-delaycontrol x))
        ((vl-eventcontrol-p x) (vl-jp-eventcontrol x))
        (t                     (vl-jp-repeateventcontrol x))))
(add-json-encoder vl-delayoreventcontrol-p vl-jp-delayoreventcontrol)
(def-vl-jp-option delayoreventcontrol)

(define vl-jp-rhs ((x vl-rhs-p) &key (ps 'ps))
  (vl-rhs-case x
    (:vl-rhsexpr (jp-object :tag (jp-sym x.kind)
                            :guts (vl-jp-expr (vl-rhsexpr->guts x))))
    (:vl-rhsnew  (jp-object :tag (jp-sym x.kind)
                            :arrsize (vl-jp-maybe-expr (vl-rhsnew->arrsize x))
                            :args (vl-jp-exprlist (vl-rhsnew->args x))))))
(add-json-encoder vl-rhs-p vl-jp-rhs)
(def-vl-jp-option rhs)

(define vl-jp-nettypename ((x vl-nettypename-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-nettypename-p)))
  (jp-ssn x))
(add-json-encoder vl-nettypename-p vl-jp-nettypename)
(def-vl-jp-option nettypename)

(define vl-jp-maybe-4vec ((x sv::maybe-4vec-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable sv::maybe-4vec-p sv::4vec-p)))
  (cond ((not x)  (jp-null))
        ((atom x) (jp-ssn x))
        (t (vl-ps-seq (vl-print "[")
                      (jp-ssn (car x))
                      (vl-print ",")
                      (jp-ssn (cdr x))
                      (vl-println? "]")))))
(add-json-encoder sv::maybe-4vec-p vl-jp-maybe-4vec)

(define vl-jp-lifetime ((x vl-lifetime-p) &key (ps 'ps)) (jp-sym x))
(add-json-encoder vl-lifetime-p vl-jp-lifetime)

(def-vl-jp-aggregate gatedelay)
(def-vl-jp-option gatedelay)

(def-vl-jp-aggregate vardecl)
(def-vl-jp-list vardecl)

(define vl-jp-paramtype ((x vl-paramtype-p) &key (ps 'ps))
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (jp-object :tag     (jp-sym x.kind)
                :range   (vl-jp-maybe-range (vl-implicitvalueparam->range x))
                :sign    (vl-jp-maybe-exprsign (vl-implicitvalueparam->sign x))
                :default (vl-jp-maybe-expr (vl-implicitvalueparam->default x))))
    (:vl-explicitvalueparam
     (jp-object :tag     (jp-sym x.kind)
                :type    (vl-jp-datatype (vl-explicitvalueparam->type x))
                :default (vl-jp-maybe-expr (vl-explicitvalueparam->default x))
                :final-value (vl-jp-maybe-4vec (vl-explicitvalueparam->final-value x))))
    (:vl-typeparam
     (jp-object :tag     (jp-sym x.kind)
                :default (vl-jp-maybe-datatype (vl-typeparam->default x))))))
(add-json-encoder vl-paramtype-p vl-jp-paramtype)

(def-vl-jp-aggregate paramdecl)
(def-vl-jp-list paramdecl)

(define vl-jp-commentmap-aux ((x vl-commentmap-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps))
    (vl-ps-seq (vl-print "[")
               (vl-jp-location (caar x))
               (vl-print ",")
               (jp-str (cdar x))
               (vl-print "]")
               (if (atom (cdr x))
                   ps
                 (vl-println? ", "))
               (vl-jp-commentmap-aux (cdr x)))))

(define vl-jp-commentmap ((x vl-commentmap-p) &key (ps 'ps))
  (vl-ps-seq (vl-print "[")
             (vl-jp-commentmap-aux x)
             (vl-println? "]")))

(add-json-encoder vl-commentmap-p vl-jp-commentmap)

(def-vl-jp-aggregate typedef)
(def-vl-jp-list typedef)

(define vl-jp-importpart ((x vl-importpart-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-importpart-p vl-jp-importpart)

(def-vl-jp-aggregate import)
(def-vl-jp-list import)

(define vl-jp-blockitem ((x vl-blockitem-p) &key (ps 'ps))
  (case (tag x)
    (:vl-vardecl   (vl-jp-vardecl x))
    (:vl-paramdecl (vl-jp-paramdecl x))
    (:vl-import    (vl-jp-import x))
    (otherwise     (vl-jp-typedef x))))
(add-json-encoder vl-blockitem-p vl-jp-blockitem)
(def-vl-jp-list blockitem)

(define vl-jp-asserttype ((x vl-asserttype-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-asserttype-p vl-jp-asserttype)

(define vl-jp-assertdeferral ((x vl-assertdeferral-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-assertdeferral-p vl-jp-assertdeferral)

(define vl-jp-distweighttype ((x vl-distweighttype-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-distweighttype-p vl-jp-distweighttype)

(def-vl-jp-aggregate distitem)
(def-vl-jp-list distitem :list-p vl-distlist-p)

(def-vl-jp-aggregate exprdist)
(def-vl-jp-list exprdist)
(def-vl-jp-option exprdist)

(define vl-jp-repetitiontype ((x vl-repetitiontype-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-repetitiontype-p vl-jp-repetitiontype)

(def-vl-jp-aggregate repetition)

(define vl-jp-property-unaryop ((x vl-property-unaryop-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-property-unaryop-p vl-jp-property-unaryop)

(define vl-jp-property-binaryop ((x vl-property-binaryop-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-property-binaryop-p vl-jp-property-binaryop)

(define vl-jp-property-acceptop ((x vl-property-acceptop-p) &key (ps 'ps)) (if (stringp x) (jp-str x) (jp-sym x)))
(add-json-encoder vl-property-acceptop-p vl-jp-property-acceptop)

(defines vl-jp-propexpr
  (define vl-jp-propexpr ((x vl-propexpr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propexpr-count x) 0)
    (vl-propexpr-case x
      (:vl-propcore
       (jp-object :tag  (jp-sym x.kind)
                  :guts (vl-jp-exprdist x.guts)))
      (:vl-propinst
       (jp-object :tag  (jp-sym x.kind)
                  :ref  (vl-jp-scopeexpr x.ref)
                  :args (vl-jp-propactuallist x.args)))
      (:vl-propthen
       (jp-object :tag   (jp-sym x.kind)
                  :delay (vl-jp-range x.delay)
                  :left  (vl-jp-propexpr x.left)
                  :right (vl-jp-propexpr x.right)))
      (:vl-proprepeat
       (jp-object :tag  (jp-sym x.kind)
                  :seq  (vl-jp-propexpr x.seq)
                  :reps (vl-jp-repetition x.reps)))
      (:vl-propassign
       (jp-object :tag   (jp-sym x.kind)
                  :seq   (vl-jp-propexpr x.seq)
                  :items (vl-jp-exprlist x.items)))
      (:vl-propthroughout
       (jp-object :tag   (jp-sym x.kind)
                  :left  (vl-jp-exprdist x.left)
                  :right (vl-jp-propexpr x.right)))
      (:vl-propclock
       (jp-object :tag     (jp-sym x.kind)
                  :trigger (vl-jp-evatomlist x.trigger)
                  :then    (vl-jp-propexpr x.then)))
      (:vl-propunary
       (jp-object :tag  (jp-sym x.kind)
                  :op   (vl-jp-property-unaryop x.op)
                  :arg  (vl-jp-propexpr x.arg)))
      (:vl-propbinary
       (jp-object :tag   (jp-sym x.kind)
                  :op    (vl-jp-property-binaryop x.op)
                  :left  (vl-jp-propexpr x.left)
                  :right (vl-jp-propexpr x.right)))
      (:vl-propalways
       (jp-object :tag  (jp-sym x.kind)
                  :strongp (jp-bool x.strongp)
                  :range (vl-jp-maybe-range x.range)
                  :prop  (vl-jp-propexpr x.prop)))
      (:vl-propeventually
       (jp-object :tag  (jp-sym x.kind)
                  :strongp (jp-bool x.strongp)
                  :range (vl-jp-maybe-range x.range)
                  :prop  (vl-jp-propexpr x.prop)))
      (:vl-propaccept
       (jp-object :tag  (jp-sym x.kind)
                  :op   (vl-jp-property-acceptop x.op)
                  :condition (vl-jp-exprdist x.condition)
                  :prop (vl-jp-propexpr x.prop)))
      (:vl-propnexttime
       (jp-object :tag  (jp-sym x.kind)
                  :strongp (jp-bool x.strongp)
                  :expr (vl-jp-maybe-expr x.expr)
                  :prop (vl-jp-propexpr x.prop)))
      (:vl-propif
       (jp-object :tag  (jp-sym x.kind)
                  :condition (vl-jp-exprdist x.condition)
                  :then (vl-jp-propexpr x.then)
                  :else (vl-jp-propexpr x.else)))
      (:vl-propcase
       (jp-object :tag  (jp-sym x.kind)
                  :condition (vl-jp-exprdist x.condition)
                  :cases (vl-jp-propcaseitemlist x.cases)))))

  (define vl-jp-propactual ((x vl-propactual-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propactual-count x) 0)
    (vl-propactual-case x
      (:blank 
       (jp-object :tag  (jp-sym x.kind)
                  :name (jp-maybe-string x.name)))
      (:event
       (jp-object :tag  (jp-sym x.kind)
                  :name (jp-maybe-string x.name)
                  :evatoms (vl-jp-evatomlist x.evatoms)))
      (:prop 
       (jp-object :tag  (jp-sym x.kind)
                  :name (jp-maybe-string x.name)
                  :prop (vl-jp-propexpr x.prop)))))
  
  (define vl-jp-propactuallist ((x vl-propactuallist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propactuallist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-propactuallist-aux x)
               (vl-println? "]")))

  (define vl-jp-propactuallist-aux ((x vl-propactuallist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propactuallist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-propactual (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-propactuallist-aux (cdr x)))))

  (define vl-jp-propcaseitem ((x vl-propcaseitem-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propcaseitem-count x) 0)
    (b* (((vl-propcaseitem x) x))
      (jp-object :tag   (jp-sym :vl-propcaseitem)
                 :match (vl-jp-exprdistlist x.match)
                 :prop  (vl-jp-propexpr x.prop))))

  (define vl-jp-propcaseitemlist ((x vl-propcaseitemlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propcaseitemlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-propcaseitemlist-aux x)
               (vl-println? "]")))

  (define vl-jp-propcaseitemlist-aux ((x vl-propcaseitemlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-propcaseitemlist-count x) 0)
    (b* (((when (atom x))
          ps))
      (vl-ps-seq (vl-jp-propcaseitem (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-propcaseitemlist-aux (cdr x)))))
) ;; defines vl-jp-propexpr

(add-json-encoder vl-propexpr-p vl-jp-propexpr)
(add-json-encoder vl-propactual-p vl-jp-propactual)
(add-json-encoder vl-propactuallist-p vl-jp-propactuallist)
(add-json-encoder vl-propcaseitem-p vl-jp-propcaseitem)
(add-json-encoder vl-propcaseitemlist-p vl-jp-propcaseitemlist)

(def-vl-jp-aggregate propspec)

(defines vl-jp-stmt
 (define vl-jp-stmt ((x vl-stmt-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-stmt-count x) 0)
   (b* ((kind (vl-stmt-kind x)))
     (vl-stmt-case x
       (:vl-nullstmt
        (jp-object :tag  (jp-sym kind)
                   :atts (vl-jp-atts x.atts)))
       (:vl-assignstmt
        (jp-object :tag    (jp-sym kind)
                   :type   (vl-jp-assign-type x.type)
                   :lvalue (vl-jp-expr x.lvalue)
                   :rhs    (vl-jp-rhs x.rhs)
                   :loc    (vl-jp-location x.loc)
                   :ctrl   (vl-jp-maybe-delayoreventcontrol x.ctrl)
                   :atts   (vl-jp-atts x.atts)))
       (:vl-deassignstmt
        (jp-object :tag    (jp-sym kind)
                   :lvalue (vl-jp-expr x.lvalue)
                   :atts   (vl-jp-atts x.atts)))
       (:vl-callstmt
        (jp-object :tag     (jp-sym kind)
                   :id      (vl-jp-scopeexpr x.id)
                   :loc     (vl-jp-location x.loc)
                   :args    (vl-jp-maybe-exprlist x.args)
                   :atts    (vl-jp-atts x.atts)
                   :typearg (vl-jp-maybe-datatype x.typearg)
                   :systemp (jp-bool x.systemp)
                   :voidp   (jp-bool x.voidp)))
       (:vl-disablestmt
        (jp-object :tag    (jp-sym kind)
                   :id     (vl-jp-scopeexpr x.id)
                   :atts   (vl-jp-atts x.atts)))
       (:vl-eventtriggerstmt
        (jp-object :tag    (jp-sym kind)
                   :id     (vl-jp-expr x.id)
                   :atts   (vl-jp-atts x.atts)))
       (:vl-casestmt
        (jp-object :tag      (jp-sym kind)
                   :test     (vl-jp-expr x.test)
                   :caselist (vl-jp-caselist x.caselist)
                   :default  (vl-jp-stmt x.default)
                   :loc      (vl-jp-location x.loc)
                   :casetype (vl-jp-casetype x.casetype)
                   :check    (vl-jp-casecheck x.check)
                   :atts     (vl-jp-atts x.atts)
                   :casekey  (vl-jp-casekey x.casekey)))
       (:vl-ifstmt
        (jp-object :tag         (jp-sym kind)
                   :condition   (vl-jp-expr x.condition)
                   :truebranch  (vl-jp-stmt x.truebranch)
                   :falsebranch (vl-jp-stmt x.falsebranch)
                   :atts        (vl-jp-atts x.atts)))
       (:vl-foreverstmt
        (jp-object :tag       (jp-sym kind)
                   :body      (vl-jp-stmt x.body)
                   :atts      (vl-jp-atts x.atts)))
       (:vl-waitstmt
        (jp-object :tag       (jp-sym kind)
                   :condition (vl-jp-expr x.condition)
                   :body      (vl-jp-stmt x.body)
                   :atts      (vl-jp-atts x.atts)))
       (:vl-repeatstmt
        (jp-object :tag       (jp-sym kind)
                   :condition (vl-jp-expr x.condition)
                   :body      (vl-jp-stmt x.body)
                   :atts      (vl-jp-atts x.atts)))
       (:vl-whilestmt
        (jp-object :tag       (jp-sym kind)
                   :condition (vl-jp-expr x.condition)
                   :body      (vl-jp-stmt x.body)
                   :atts      (vl-jp-atts x.atts)))
       (:vl-dostmt
        (jp-object :tag       (jp-sym kind)
                   :condition (vl-jp-expr x.condition)
                   :body      (vl-jp-stmt x.body)
                   :atts      (vl-jp-atts x.atts)))
       (:vl-forstmt
        (jp-object :tag         (jp-sym kind)
                   :test        (vl-jp-expr x.test)
                   :stepforms   (vl-jp-stmtlist x.stepforms)
                   :body        (vl-jp-stmt x.body)
                   :initdecls   (vl-jp-vardecllist x.initdecls)
                   :initassigns (vl-jp-stmtlist x.initassigns)
                   :atts        (vl-jp-atts x.atts)))
       (:vl-foreachstmt
        (jp-object :tag         (jp-sym kind)
                   :array       (vl-jp-scopeexpr x.array)
                   :loopvars    (jp-maybe-string-list x.loopvars)
                   :vardecls    (vl-jp-vardecllist x.vardecls)
                   :body        (vl-jp-stmt x.body)
                   :atts        (vl-jp-atts x.atts)))
       (:vl-breakstmt
        (jp-object :tag    (jp-sym kind)
                   :atts   (vl-jp-atts x.atts)))
       (:vl-continuestmt
        (jp-object :tag    (jp-sym kind)
                   :atts   (vl-jp-atts x.atts)))
       (:vl-blockstmt
        (jp-object :tag        (jp-sym kind)
                   :blocktype  (jp-sym x.blocktype)
                   :stmts      (vl-jp-stmtlist x.stmts)
                   :name       (jp-maybe-string x.name)
                   :atts       (vl-jp-atts x.atts)
                   :vardecls   (vl-jp-vardecllist x.vardecls)
                   :paramdecls (vl-jp-paramdecllist x.paramdecls)
                   :typedefs   (vl-jp-typedeflist x.typedefs)
                   :imports    (vl-jp-importlist x.imports)
                   :loaditems  (vl-jp-blockitemlist x.loaditems)))
       (:vl-timingstmt
        (jp-object :tag  (jp-sym kind)
                   :ctrl (vl-jp-delayoreventcontrol x.ctrl)
                   :body (vl-jp-stmt x.body)
                   :atts (vl-jp-atts x.atts)))
       (:vl-returnstmt
        (jp-object :tag    (jp-sym kind)
                   :val    (vl-jp-maybe-expr x.val)
                   :atts   (vl-jp-atts x.atts)
                   :loc    (vl-jp-location x.loc)))
       (:vl-assertstmt
        (jp-object :tag       (jp-sym kind)
                   :assertion (vl-jp-assertion x.assertion)
                   :atts      (vl-jp-atts x.atts)))
       (:vl-cassertstmt
        (jp-object :tag        (jp-sym kind)
                   :cassertion (vl-jp-cassertion x.cassertion)
                   :atts       (vl-jp-atts x.atts))))))

 (define vl-jp-assertion ((x vl-assertion-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-assertion-count x) 0)
   (b* (((vl-assertion y) x))
     (jp-object :tag       (jp-sym :vl-assertion)
                :name      (jp-maybe-string      y.name)
                :type      (vl-jp-asserttype     y.type)
                :deferral  (vl-jp-assertdeferral y.deferral)
                :condition (vl-jp-expr           y.condition)
                :success   (vl-jp-stmt           y.success)
                :failure   (vl-jp-stmt           y.failure)
                :loc       (vl-jp-location       y.loc))))

 (define vl-jp-cassertion ((x vl-cassertion-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-cassertion-count x) 0)
   (b* (((vl-cassertion y) x))
     (jp-object :tag       (jp-sym :vl-cassertion)
                :name      (jp-maybe-string      y.name)
                :type      (vl-jp-asserttype     y.type)
                :sequencep (jp-bool              y.sequencep)
                :condition (vl-jp-propspec       y.condition)
                :success   (vl-jp-stmt           y.success)
                :failure   (vl-jp-stmt           y.failure)
                :loc       (vl-jp-location       y.loc))))

 (define vl-jp-stmtlist ((x vl-stmtlist-p) &key (ps 'ps))
   ;; Print the stmtessions as a JSON array with brackets.
   :measure (two-nats-measure (vl-stmtlist-count x) 1)
   (vl-ps-seq (vl-print "[")
              (vl-jp-stmtlist-aux x)
              (vl-println? "]")))

 (define vl-jp-stmtlist-aux ((x vl-stmtlist-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-stmtlist-count x) 0)
   (b* (((when (atom x))
         ps))
     (vl-ps-seq (vl-jp-stmt (car x))
                (if (atom (cdr x))
                    ps
                  (vl-println? ", "))
                (vl-jp-stmtlist-aux (cdr x)))))

 (define vl-jp-caselist ((x vl-caselist-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-caselist-count x) 1)
   (vl-ps-seq (vl-print "[")
              (vl-jp-caselist-aux x)
              (vl-println? "]")))

 (define vl-jp-caselist-aux ((x vl-caselist-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-caselist-count x) 0)
   (b* ((x (vl-caselist-fix x))
        ((when (atom x))
         ps)
        ((cons exprs stmt1) (car x)))
     (vl-ps-seq (vl-print "[")
                (vl-jp-exprlist exprs)
                (vl-println? ",")
                (vl-jp-stmt stmt1)
                (vl-println? "]")
                (if (atom (cdr x))
                    ps
                  (vl-println? ", "))
                (vl-jp-caselist-aux (cdr x))))))

(add-json-encoder vl-stmt-p vl-jp-stmt)
(add-json-encoder vl-assertion-p vl-jp-assertion)
(add-json-encoder vl-cassertion-p vl-jp-cassertion)
(add-json-encoder vl-stmtlist-p vl-jp-stmtlist)
(add-json-encoder vl-caselist-p vl-jp-caselist)

;;;;;;; end big vl-stmt mutual-recursion and encoders..

;; building to modules..

(define vl-jp-syntaxversion ((x vl-syntaxversion-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-syntaxversion-p)))
  (jp-ssn x))

(add-json-encoder vl-syntaxversion-p vl-jp-syntaxversion)

(define vl-jp-stringlist-aux ((x string-listp) &key (ps 'ps))
  (if (atom x) ps
    (vl-ps-seq (jp-ssn (car x))
               (if (atom (cdr x))
                   ps
                 (vl-println? ", "))
               (vl-jp-stringlist-aux (cdr x)))))

(define vl-jp-stringlist ((x string-listp) &key (ps 'ps))
  (vl-ps-seq (vl-print "[")
             (vl-jp-stringlist-aux x)
             (vl-println? "]")))

(add-json-encoder string-listp vl-jp-stringlist)
  
(def-vl-jp-aggregate interfaceport)
(def-vl-jp-aggregate regularport)

(define vl-jp-port ((x vl-port-p) &key (ps 'ps))
  (case (tag x)
    (:vl-regularport (vl-jp-regularport x))
    (otherwise       (vl-jp-interfaceport x))))

(add-json-encoder vl-port-p vl-jp-port)
(def-vl-jp-list port)

(def-vl-jp-aggregate portdecl)
(def-vl-jp-list portdecl)

(def-vl-jp-aggregate plainarg)
(def-vl-jp-list plainarg)

(def-vl-jp-aggregate namedarg)
(def-vl-jp-list namedarg)

(define vl-jp-arguments ((x vl-arguments-p) &key (ps 'ps))
  (vl-arguments-case x
    (:vl-arguments-plain 
     (jp-object :tag (jp-sym x.kind)
                :args (vl-jp-plainarglist (vl-arguments-plain->args x))))
    (:vl-arguments-named
     (jp-object :tag (jp-sym x.kind)
                :args (vl-jp-namedarglist (vl-arguments-named->args x))
                :starp (jp-bool (vl-arguments-named->starp x))))))

(add-json-encoder vl-arguments-p vl-jp-arguments)

(define vl-jp-paramvalue ((x vl-paramvalue-p) &key (ps 'ps))
  (vl-paramvalue-case x
    (:type
     (jp-object :tag (jp-sym x.kind)
                :args (vl-jp-datatype (vl-paramvalue-type->type x))))
    (:expr
     (jp-object :tag (jp-sym x.kind)
                :args (vl-jp-expr (vl-paramvalue-expr->expr x))))))

(add-json-encoder vl-paramvalue-p vl-jp-paramvalue)

(def-vl-jp-list paramvalue)
(def-vl-jp-option paramvalue)

(def-vl-jp-aggregate namedparamvalue)
(def-vl-jp-list namedparamvalue)

(define vl-jp-paramargs ((x vl-paramargs-p) &key (ps 'ps))
  (vl-paramargs-case x
    (:vl-paramargs-plain 
     (jp-object :tag (jp-sym x.kind)
                :args (vl-jp-paramvaluelist (vl-paramargs-plain->args x))))
    (:vl-paramargs-named
     (jp-object :tag (jp-sym x.kind)
                :args (vl-jp-namedparamvaluelist (vl-paramargs-named->args x))))))

(add-json-encoder vl-paramargs-p vl-jp-paramargs)

(def-vl-jp-aggregate gatestrength)
(def-vl-jp-option gatestrength)

(def-vl-jp-aggregate modinst)
(def-vl-jp-list modinst)

(def-vl-jp-aggregate assign)
(def-vl-jp-list assign)

(def-vl-jp-aggregate gateinst)
(def-vl-jp-list gateinst)

(define vl-jp-timeunit ((x vl-timeunit-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-timeunit-p)))
  (jp-ssn x))
(add-json-encoder vl-timeunit-p vl-jp-timeunit)
(def-vl-jp-aggregate timeliteral)
(def-vl-jp-option timeliteral)
(def-vl-jp-aggregate timeunitdecl)
(def-vl-jp-option timeunitdecl)
(def-vl-jp-aggregate timeprecisiondecl)
(def-vl-jp-option timeprecisiondecl)

(def-vl-jp-aggregate always)
(def-vl-jp-list always)
(def-vl-jp-aggregate initial)
(def-vl-jp-list initial)
(def-vl-jp-aggregate final)
(def-vl-jp-list final)
(def-vl-jp-aggregate genvar)
(def-vl-jp-list genvar)
(def-vl-jp-aggregate fundecl :omit (function constraints loaditems))
(def-vl-jp-list fundecl)
(def-vl-jp-aggregate taskdecl :omit (loaditems))
(def-vl-jp-list taskdecl)
(def-vl-jp-aggregate alias)
(def-vl-jp-list alias)
(def-vl-jp-list assertion)
(def-vl-jp-list cassertion)
(def-vl-jp-aggregate propport)
(def-vl-jp-list propport)
(def-vl-jp-aggregate property)
(def-vl-jp-aggregate sequence)
(def-vl-jp-list property)
(def-vl-jp-list sequence)

(define vl-jp-scopeid ((x vl-scopeid-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-scopeid-p)))
  (jp-ssn x))
(add-json-encoder vl-scopeid-p vl-jp-scopeid)
(def-vl-jp-option scopeid)

(defines vl-jp-genelement
  (define vl-jp-genelement ((x vl-genelement-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-genelement-count x) 0)
    (vl-genelement-case x
      (:vl-genbase (jp-object :tag (jp-sym x.kind)
                              ;; BOZO -- leaving this out for now..
                              ;; :item (vl-jp-modelelement x.item)))
                              ))
      (:vl-genbegin (jp-object :tag (jp-sym x.kind)
                               :block (vl-jp-genblock x.block)))
      (:vl-genif (jp-object :tag (jp-sym x.kind)
                            :test (vl-jp-expr x.test)
                            :then (vl-jp-genblock x.then)
                            :else (vl-jp-genblock x.else)
                            :loc (vl-jp-location x.loc)))
      (:vl-gencase (jp-object :tag (jp-sym x.kind)
                              :test (vl-jp-expr x.test)
                              :cases (vl-jp-gencaselist x.cases)
                              :default (vl-jp-genblock x.default)
                              :loc (vl-jp-location x.loc)))
      (:vl-genloop (jp-object :tag (jp-sym x.kind)
                              :var (jp-str x.var)
                              :genvarp (jp-bool x.genvarp)
                              :initval (vl-jp-expr x.initval)
                              :continue (vl-jp-expr x.continue)
                              :nextval (vl-jp-expr x.nextval)
                              :body (vl-jp-genblock x.body)
                              :loc (vl-jp-location x.loc)))
      (:vl-genarray (jp-object :tag (jp-sym x.kind)
                               :name (jp-maybe-string x.name)
                               :var (jp-str x.var)
                               :genvarp (jp-bool x.genvarp)
                               :blocks (vl-jp-genblocklist x.blocks)
                               :loc (vl-jp-location x.loc)))))
  
  (define vl-jp-genblock ((x vl-genblock-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-genblock-count x) 0)
    (b* (((vl-genblock x) x))
      (jp-object :tag (jp-sym :vl-genblock)
                 :name (vl-jp-maybe-scopeid x.name)
                 :elems (vl-jp-genelementlist x.elems)
                 :condnestp (jp-bool x.condnestp)
                 :loc (vl-jp-location x.loc))))
  
  (define vl-jp-genelementlist ((x vl-genelementlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-genelementlist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-genelementlist-aux x)
               (vl-println? "]")))
  
  (define vl-jp-genelementlist-aux ((x vl-genelementlist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-genelementlist-count x) 0)
    (if (atom x) ps
      (vl-ps-seq (vl-jp-genelement (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-genelementlist-aux (cdr x)))))

  (define vl-jp-genblocklist ((x vl-genblocklist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-genblocklist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-genblocklist-aux x)
               (vl-println? "]")))
  
  (define vl-jp-genblocklist-aux ((x vl-genblocklist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-genblocklist-count x) 0)
    (if (atom x) ps
      (vl-ps-seq (vl-jp-genblock (car x))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-genblocklist-aux (cdr x)))))

  (define vl-jp-gencaselist ((x vl-gencaselist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-gencaselist-count x) 1)
    (vl-ps-seq (vl-print "[")
               (vl-jp-gencaselist-aux x)
               (vl-println? "]")))
  
  (define vl-jp-gencaselist-aux ((x vl-gencaselist-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-gencaselist-count x) 0)
    (b* (((when (atom x)) ps)
         ((when (mbe :logic (not (vl-gencaselist-p x)) :exec nil)) ps))
      (vl-ps-seq (vl-print "[")
                 (vl-jp-exprlist (caar x))
                 (vl-print ",")
                 (vl-jp-genblock (cdar x))
                 (vl-print "]")
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-gencaselist-aux (cdr x)))))
) ;; defines vl-jp-genelement

(add-json-encoder vl-genelementlist-p vl-jp-genelementlist)

(define vl-jp-dpispec ((x vl-dpispec-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-dpispec-p)))
  (jp-ssn x))
(add-json-encoder vl-dpispec-p vl-jp-dpispec)
(define vl-jp-dpiprop ((x vl-dpiprop-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-dpiprop-p)))
  (jp-ssn x))
(add-json-encoder vl-dpiprop-p vl-jp-dpiprop)
(define vl-jp-dpifntask ((x vl-dpifntask-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-dpifntask-p)))
  (jp-ssn x))
(add-json-encoder vl-dpifntask-p vl-jp-dpifntask)

(def-vl-jp-aggregate dpiimport)
(def-vl-jp-list dpiimport)
(def-vl-jp-aggregate dpiexport)
(def-vl-jp-list dpiexport)
(def-vl-jp-aggregate clkskew)
(def-vl-jp-option clkskew)
(def-vl-jp-aggregate clkassign)
(def-vl-jp-list clkassign)
(def-vl-jp-aggregate clkdecl)
(def-vl-jp-list clkdecl)
(def-vl-jp-aggregate gclkdecl)
(def-vl-jp-list gclkdecl)
(def-vl-jp-aggregate defaultdisable)
(def-vl-jp-list defaultdisable)
(def-vl-jp-aggregate covergroup)
(def-vl-jp-list covergroup)
(def-vl-jp-aggregate elabtask)
(def-vl-jp-list elabtask)
(def-vl-jp-aggregate ansi-portdecl)
(def-vl-jp-list ansi-portdecl)
(def-vl-jp-aggregate parse-temps)
(def-vl-jp-option parse-temps)
(def-vl-jp-aggregate bind)
(def-vl-jp-list bind)
(def-vl-jp-aggregate class)
(def-vl-jp-list class)

(def-vl-jp-aggregate module :omit (params))
(def-vl-jp-option module)
(def-vl-jp-list module)

;; building to udps..

(define vl-jp-udpsymbol ((x vl-udpsymbol-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-udpsymbol-p)))
  (jp-ssn x))
(add-json-encoder vl-udpsymbol-p vl-jp-udpsymbol)
(def-vl-jp-option udpsymbol :option-p vl-maybe-udpsymbol-p-p)
(def-vl-jp-aggregate udpedge)
(define vl-jp-udpentry ((x vl-udpentry-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-udpentry-p)))
  (cond ((vl-udpsymbol-p x) (vl-jp-udpsymbol x))
        (t (vl-jp-udpedge x))))
(add-json-encoder vl-udpentry-p vl-jp-udpentry)
(def-vl-jp-list udpentry)
(def-vl-jp-aggregate udpline)
(def-vl-jp-list udpline :list-p vl-udptable-p)
(def-vl-jp-aggregate udp)
(def-vl-jp-list udp)

;; building to interfaces..

(def-vl-jp-aggregate modport-port)
(def-vl-jp-list modport-port)
(def-vl-jp-aggregate modport)
(def-vl-jp-list modport)
(def-vl-jp-aggregate interface :omit (params))
(def-vl-jp-list interface)

;; final building to design..

(def-vl-jp-aggregate program)
(def-vl-jp-list program)
(def-vl-jp-aggregate package)
(def-vl-jp-list package)
(def-vl-jp-aggregate config)
(def-vl-jp-list config)
(define vl-jp-fwdtypedefkind ((x vl-fwdtypedefkind-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-fwdtypedefkind-p)))
  (jp-ssn x))
(add-json-encoder vl-fwdtypedefkind-p vl-jp-fwdtypedefkind)
(def-vl-jp-aggregate fwdtypedef)
(def-vl-jp-list fwdtypedef)

(def-vl-jp-aggregate design)


#|

(in-package "ACL2")

;;(include-book "oslib/top"             :dir :system)
;;(include-book "centaur/vl/loader/top" :dir :system)
;;(include-book "centaur/vl/util/print" :dir :system)
;;(include-book "centaur/vl/mlib/json"  :dir :system)

(encapsulate 
 (((compute-vl-conf *) => * 
   :formals (mod) 
   :guard (stringp mod)))

 (local (defun compute-vl-conf (mod)
          (declare (xargs :guard (stringp mod)) (ignore mod))
          (vl::make-vl-loadconfig :start-files (list "") :search-path '())))
 
 (defthm compute-vl-conf-returns-vl-loadconfig
   (vl::vl-loadconfig-p (compute-vl-conf mod))))

;; The following function is the default name for a function
;; which we use to map mod-name to a vl-config object which is
;; used to read in the design:
;;
(define compute-vl-conf-inst ((mod stringp))
  :returns (rslt vl::vl-loadconfig-p)
  (b* ((v-file mod))
    (vl::make-vl-loadconfig :start-files (list v-file) :search-path '("lib"))))

(defattach compute-vl-conf compute-vl-conf-inst)

(define vl->json ((base-name stringp)
                  (json-file stringp)
                  state)
  (b* ((vl-config               (compute-vl-conf base-name))
       ((mv loadresult state)   (vl::vl-load vl-config))
       ((vl::vl-loadresult res) loadresult))
    (vl::with-ps-file json-file
       (vl::vl-ps-update-autowrap-col 120)
       (vl::vl-ps-update-autowrap-ind 10)
       (vl::vl-jp-design res.design))))

|#
