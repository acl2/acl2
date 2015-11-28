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
to convert @(see vl2014) @(see syntax) into nice JSON data, but are somewhat
flexible and may be useful for other applications.</p>")


(defsection json-encoders
  :parents (json-printing)
  :short "A table of JSON encoders to use for for different kinds of data."
  :long "<p>A JSON encoder is a function of the following signature:</p>

@({ encode-foo : foo * ps --> ps })

<p>Where @('foo') is expected to be an object of some type @('foop'), and
@('ps') is the @(see vl2014) @(see printer) state stobj, @(see ps).  Each such
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
    (vl-print "null")))

(add-json-encoder maybe-stringp jp-maybe-string)



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
    (vl-print-str "null")))

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
basic enumerations like @(see vl-exprtype-p).  We print only the symbol name,
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
             (second forms)
             (if (atom (cddr forms))
                 nil
               (cons `(vl-println? ", ")
                     (jp-object-aux (cddr forms)))))))

  (defmacro jp-object (&rest forms)
    `(vl-ps-seq (vl-print "{")
                ,@(jp-object-aux forms)
                (vl-println? "}"))))



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

(define def-vl-jp-aggregate-fn (type omit overrides long newlines world)
  (b* ((mksym-package-symbol 'vl2014::foo)
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

(logic)


(defmacro def-vl-jp-list (type &key newlines)
  (declare (xargs :guard (maybe-natp newlines)))
  (b* ((mksym-package-symbol 'vl2014::foo)
       (list-p         (mksym 'vl- type 'list-p))
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



;; Real Verilog JSON Encoding

(define vl-jp-exprtype ((x vl-exprtype-p) &key (ps 'ps))
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


(define vl-jp-alwaystype ((x vl-alwaystype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(add-json-encoder vl-exprtype-p         vl-jp-exprtype)
(add-json-encoder vl-cstrength-p        vl-jp-cstrength)
(add-json-encoder vl-dstrength-p        vl-jp-dstrength)
(add-json-encoder vl-direction-p        vl-jp-direction)
(add-json-encoder vl-gatetype-p         vl-jp-gatetype)
(add-json-encoder vl-evatomtype-p       vl-jp-evatomtype)
(add-json-encoder vl-assign-type-p      vl-jp-assign-type)
(add-json-encoder vl-deassign-type-p    vl-jp-deassign-type)
(add-json-encoder vl-casetype-p         vl-jp-casetype)
(add-json-encoder vl-casecheck-p        vl-jp-casecheck)
(add-json-encoder vl-alwaystype-p       vl-jp-alwaystype)


(define vl-jp-maybe-exprtype ((x vl-maybe-exprtype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (if x
      (vl-jp-exprtype x)
    (vl-print "null")))

(define vl-jp-maybe-cstrength ((x vl-maybe-cstrength-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (if x
      (vl-jp-cstrength x)
    (vl-print "null")))

(define vl-jp-maybe-direction ((x vl-maybe-direction-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (if x
      (vl-jp-direction x)
    (vl-print "null")))

(add-json-encoder vl-maybe-exprtype-p  vl-jp-maybe-exprtype)
(add-json-encoder vl-maybe-cstrength-p vl-jp-maybe-cstrength)
(add-json-encoder vl-maybe-direction-p vl-jp-maybe-direction)

(def-vl-jp-aggregate location)

#||
(top-level
 (vl-cw-ps-seq (vl-jp-location *vl-fakeloc*)))
||#



(def-vl-jp-aggregate constint
  :override ((value . jp-bignat))
  :long "<p>Note that we always encode the value as a string.  This is
because it is quite common for Verilog constants to run into the hundreds
of bits, but the JSON standard doesn't really ever say how big of numbers
must be supported and JSON implementations often use machine integers
which could not hold such large values.</p>")

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

(define jp-keygutstype ((x vl-keygutstype-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see vl-keygutstype-p) as a JSON string."
  (jp-str (vl-keygutstype->string x)))

(add-json-encoder vl-keygutstype-p jp-keygutstype)

(define jp-basictypekind ((x vl-basictypekind-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see vl-basictypekind-p) as a JSON string."
  (jp-str (vl-basictypekind->string x)))

(add-json-encoder vl-basictypekind-p jp-basictypekind)


(def-vl-jp-aggregate weirdint)
(def-vl-jp-aggregate string)
(def-vl-jp-aggregate real)
(def-vl-jp-aggregate id)
(def-vl-jp-aggregate hidpiece)
(def-vl-jp-aggregate sysfunname)
(def-vl-jp-aggregate tagname)
(def-vl-jp-aggregate funname)
(def-vl-jp-aggregate typename)
(def-vl-jp-aggregate keyguts)
(def-vl-jp-aggregate extint)
(def-vl-jp-aggregate time)
(def-vl-jp-aggregate basictype)


(define vl-jp-atomguts ((x vl-atomguts-p) &key (ps 'ps))
  :parents (vl-jp-expr vl-atomguts-p)
  :guard-hints (("Goal" :in-theory (enable vl-atomguts-p)))
  (case (tag x)
    (:vl-id         (vl-jp-id x))
    (:vl-constint   (vl-jp-constint x))
    (:vl-weirdint   (vl-jp-weirdint x))
    (:vl-string     (vl-jp-string x))
    (:vl-real       (vl-jp-real x))
    (:vl-hidpiece   (vl-jp-hidpiece x))
    (:vl-funname    (vl-jp-funname x))
    (:vl-typename   (vl-jp-typename x))
    (:vl-keyguts    (vl-jp-keyguts x))
    (:vl-extint     (vl-jp-extint x))
    (:vl-time       (vl-jp-time x))
    (:vl-basictype  (vl-jp-basictype x))
    (:vl-tagname    (vl-jp-tagname x))
    (otherwise      (vl-jp-sysfunname x))))

(add-json-encoder vl-atomguts-p vl-jp-atomguts)

(defines vl-jp-expr
  :parents (json-encoders)

  (define vl-jp-expr ((x vl-expr-p) &key (ps 'ps))
    :measure (two-nats-measure (vl-expr-count x) 0)
    (vl-expr-case x
      :atom
      (jp-object :tag (jp-sym :atom)
                 :guts (vl-jp-atomguts x.guts)
                 :finalwidth (jp-maybe-nat x.finalwidth)
                 :finaltype (vl-jp-maybe-exprtype x.finaltype))
      :nonatom
      (jp-object :tag        (jp-sym :nonatom)
                 :atts       (vl-jp-atts x.atts)
                 :args       (vl-jp-exprlist x.args)
                 :finalwidth (jp-maybe-nat x.finalwidth)
                 :finaltype  (vl-jp-maybe-exprtype x.finaltype))))

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
                     (vl-jp-expr val1)
                   (vl-print "null"))
                 (if (atom (cdr x))
                     ps
                   (vl-println? ", "))
                 (vl-jp-atts-aux (cdr x)))))

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
                 (vl-jp-exprlist-aux (cdr x))))))

(define vl-jp-maybe-expr ((x vl-maybe-expr-p) &key (ps 'ps))
  (if x
      (vl-jp-expr x)
    (vl-print "null")))

(add-json-encoder vl-expr-p       vl-jp-expr)
(add-json-encoder vl-exprlist-p   vl-jp-exprlist)
(add-json-encoder vl-atts-p       vl-jp-atts)
(add-json-encoder vl-maybe-expr-p vl-jp-maybe-expr)

(def-vl-jp-aggregate range)
(def-vl-jp-list range)

(define vl-jp-maybe-range ((x vl-maybe-range-p) &key (ps 'ps))
  (if x
      (vl-jp-range x)
    (vl-print "null")))

(add-json-encoder vl-maybe-range-p vl-jp-maybe-range)

(define vl-jp-packeddimension ((x vl-packeddimension-p) &key (ps 'ps))
  :parents (json-encoders)
  (if (eq x :vl-unsized-dimension)
      (jp-sym x)
    (vl-jp-range x)))

(add-json-encoder vl-packeddimension-p vl-jp-packeddimension)
(def-vl-jp-list packeddimension)

(define vl-jp-maybe-packeddimension ((x vl-maybe-packeddimension-p) &key (ps 'ps))
  :parents (json-encoders)
  (if x
      (vl-jp-packeddimension x)
    (vl-print "null")))

(add-json-encoder vl-maybe-packeddimension-p vl-jp-maybe-packeddimension)

(def-vl-jp-aggregate interfaceport)
(def-vl-jp-list interfaceport :newlines 4)

(def-vl-jp-aggregate regularport)
(def-vl-jp-list regularport :newlines 4)

(define vl-jp-port ((x vl-port-p) &key (ps 'ps))
  :parents (json-encoders vl-port)
  (b* ((x (vl-port-fix x)))
    (if (eq (tag x) :vl-interfaceport)
        (vl-jp-interfaceport x)
      (vl-jp-regularport x))))

(def-vl-jp-list port :newlines 4)


(def-vl-jp-aggregate gatedelay)

(define vl-jp-maybe-gatedelay ((x vl-maybe-gatedelay-p) &key (ps 'ps))
  :parents (json-encoders vl-maybe-gatedelay-p)
  (if x
      (vl-jp-gatedelay x)
    (vl-print "null")))

(add-json-encoder vl-maybe-gatedelay-p vl-jp-maybe-gatedelay)

(def-vl-jp-aggregate plainarg)
(def-vl-jp-list plainarg :newlines 4)

(def-vl-jp-aggregate namedarg)
(def-vl-jp-list namedarg :newlines 4)



(define vl-jp-lifetime ((x vl-lifetime-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-randomqualifier ((x vl-randomqualifier-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-nettypename ((x vl-nettypename-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-coretypename ((x vl-coretypename-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(add-json-encoder vl-lifetime-p         vl-jp-lifetime)
(add-json-encoder vl-randomqualifier-p  vl-jp-randomqualifier)
(add-json-encoder vl-nettypename-p      vl-jp-nettypename)
(add-json-encoder vl-coretypename-p     vl-jp-coretypename)

(define vl-jp-maybe-nettypename ((x vl-maybe-nettypename-p) &key (ps 'ps))
  :parents (json-encoders)
  (if x
      (vl-jp-nettypename x)
    (vl-print "null"))
  ///
  (add-json-encoder vl-maybe-nettypename-p vl-jp-maybe-nettypename))

(define vl-jp-enumbasekind ((x vl-enumbasekind-p) &key (ps 'ps))
  :guard-hints(("Goal" :in-theory (enable vl-enumbasekind-p)))
  (if (stringp x)
      (jp-object :tag (jp-sym :user-defined-type)
                 :name (jp-str x))
    (jp-sym x)))

(add-json-encoder vl-enumbasekind-p vl-jp-enumbasekind)

(def-vl-jp-aggregate enumbasetype)
(def-vl-jp-aggregate enumitem)
(def-vl-jp-list enumitem)


(defines vl-jp-datatype

 (define vl-jp-datatype ((x vl-datatype-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-datatype-count x) 0)
   (vl-datatype-case x
     :vl-coretype
     (jp-object :tag     (jp-sym :vl-coretype)
                :name    (vl-jp-coretypename x.name)
                :signedp (jp-bool x.signedp)
                :pdims    (vl-jp-packeddimensionlist x.pdims)
                :udims    (vl-jp-packeddimensionlist x.udims))
     :vl-struct
     (jp-object :tag     (jp-sym :vl-struct)
                :packedp (jp-bool x.packedp)
                :signedp (jp-bool x.signedp)
                :pdims    (vl-jp-packeddimensionlist x.pdims)
                :udims    (vl-jp-packeddimensionlist x.udims)
                :members (vl-jp-structmemberlist x.members))
     :vl-union
     (jp-object :tag     (jp-sym :vl-union)
                :packedp (jp-bool x.packedp)
                :signedp (jp-bool x.signedp)
                :taggedp (jp-bool x.taggedp)
                :pdims    (vl-jp-packeddimensionlist x.pdims)
                :udims    (vl-jp-packeddimensionlist x.udims)
                :members (vl-jp-structmemberlist x.members))
     :vl-enum
     (jp-object :tag      (jp-sym :vl-enum)
                :basetype (vl-jp-enumbasetype x.basetype)
                :items    (vl-jp-enumitemlist x.items)
                :pdims    (vl-jp-packeddimensionlist x.pdims)
                :udims    (vl-jp-packeddimensionlist x.udims))
     :vl-usertype
     (jp-object :tag      (jp-sym :vl-usertype)
                :kind     (vl-jp-expr x.kind)
                :pdims    (vl-jp-packeddimensionlist x.pdims)
                :udims    (vl-jp-packeddimensionlist x.udims))))

 (define vl-jp-structmemberlist ((x vl-structmemberlist-p) &key (ps 'ps))
   ;; Print the stmtessions as a JSON array with brackets.
   :measure (two-nats-measure (vl-structmemberlist-count x) 1)
   (vl-ps-seq (vl-print "[")
              (vl-jp-structmemberlist-aux x)
              (vl-println? "]")))

 (define vl-jp-structmemberlist-aux ((x vl-structmemberlist-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-structmemberlist-count x) 0)
   (if (atom x)
       ps
     (vl-ps-seq (vl-jp-structmember (car x))
                (if (atom (cdr x))
                    ps
                  (vl-println? ", "))
                (vl-jp-structmemberlist-aux (cdr x)))))

 (define vl-jp-structmember ((x vl-structmember-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-structmember-count x) 0)
   (b* (((vl-structmember x) x))
     (jp-object :tag      (jp-sym :vl-structmember)
                :atts     (vl-jp-atts x.atts)
                :rand     (vl-jp-randomqualifier x.rand)
                :rhs      (vl-jp-maybe-expr x.rhs)
                :type     (vl-jp-datatype x.type)))))

(add-json-encoder vl-datatype-p vl-jp-datatype)
(add-json-encoder vl-structmember-p vl-jp-structmember)
(add-json-encoder vl-structmemberlist-p vl-jp-structmemberlist)

(define vl-jp-maybe-datatype ((x vl-maybe-datatype-p) &key (ps 'ps))
  (if x
      (vl-jp-datatype x)
    (vl-print "null")))

(add-json-encoder vl-maybe-datatype-p vl-jp-maybe-datatype)

(def-vl-jp-aggregate vardecl)
(def-vl-jp-list vardecl :newlines 4)


(define vl-jp-paramtype ((x vl-paramtype-p) &key (ps 'ps))
   (vl-paramtype-case x
     (:vl-implicitvalueparam
      (jp-object :tag     (jp-sym :vl-implicitvalueparam)
                 :sign    (jp-sym x.sign)
                 :range   (vl-jp-maybe-range x.range)
                 :default (vl-jp-maybe-expr x.default)))
     (:vl-explicitvalueparam
      (jp-object :tag     (jp-sym :vl-explicitvalueparam)
                 :type    (vl-jp-datatype x.type)
                 :default (vl-jp-maybe-expr x.default)))
     (:vl-typeparam
      (jp-object :tag     (jp-sym :vl-typeparam)
                 :default (vl-jp-maybe-datatype x.default)))))

(add-json-encoder vl-paramtype-p vl-jp-paramtype)

(def-vl-jp-aggregate paramdecl)
(def-vl-jp-list paramdecl :newlines 4)

(define vl-jp-importpart ((x vl-importpart-p) &key (ps 'ps))
  :guard-hints(("Goal" :in-theory (enable vl-importpart-p)))
  (b* ((x (vl-importpart-fix x)))
    (if (eq x :vl-import*)
        (jp-str "*")
      (jp-str x))))

(add-json-encoder vl-importpart-p vl-jp-importpart)

(def-vl-jp-aggregate import)
(def-vl-jp-list import :newlines 4)


(define vl-jp-arguments ((x vl-arguments-p) &key (ps 'ps))
  :parents (json-encoders vl-arguments-p)
  (vl-arguments-case x
    :vl-arguments-named
    (jp-object :tag    (jp-sym :vl-arguments)
               :namedp (jp-bool t)
               :starp  (jp-bool x.starp)
               :args   (vl-jp-namedarglist x.args))
    :vl-arguments-plain
    (jp-object :tag    (jp-sym :vl-arguments)
               :namedp (jp-bool nil)
               :args   (vl-jp-plainarglist x.args))))

(add-json-encoder vl-arguments-p vl-jp-arguments)

(def-vl-jp-aggregate gatestrength)

(define vl-jp-maybe-gatestrength ((x vl-maybe-gatestrength-p) &key (ps 'ps))
  (if x
      (vl-jp-gatestrength x)
    (vl-print "null")))

(add-json-encoder vl-maybe-gatestrength-p vl-jp-maybe-gatestrength)




(define vl-jp-paramvalue ((x vl-paramvalue-p) &key (ps 'ps))
  :parents (json-encoders vl-paramvalue-p)
  (b* ((x (vl-paramvalue-fix x)))
    (vl-paramvalue-case x
      :expr     (vl-jp-expr x)
      :datatype (vl-jp-datatype x))))

(add-json-encoder vl-paramvalue-p vl-jp-paramvalue)

(def-vl-jp-list paramvalue)

(define vl-jp-maybe-paramvalue ((x vl-maybe-paramvalue-p) &key (ps 'ps))
  (if x
      (vl-jp-paramvalue x)
    (vl-print "null")))

(add-json-encoder vl-maybe-paramvalue-p vl-jp-maybe-paramvalue)

(def-vl-jp-aggregate namedparamvalue)
(def-vl-jp-list namedparamvalue)

(define vl-jp-paramargs ((x vl-paramargs-p) &key (ps 'ps))
  (vl-paramargs-case x
    :vl-paramargs-named
    (jp-object :tag    (jp-sym :vl-paramargs)
               :namedp (jp-bool t)
               :args   (vl-jp-namedparamvaluelist x.args))
    :vl-paramargs-plain
    (jp-object :tag    (jp-sym :vl-paramargs)
               :namedp (jp-bool nil)
               :args   (vl-jp-paramvaluelist x.args))))

(add-json-encoder vl-paramargs-p vl-jp-paramargs)

(def-vl-jp-aggregate modinst)
(def-vl-jp-list modinst)

(def-vl-jp-aggregate gateinst)
(def-vl-jp-list gateinst)

(def-vl-jp-aggregate delaycontrol)
(def-vl-jp-aggregate evatom)
(def-vl-jp-list evatom)

(def-vl-jp-aggregate eventcontrol)
(def-vl-jp-aggregate repeateventcontrol)


(define vl-jp-delayoreventcontrol ((x vl-delayoreventcontrol-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-delayoreventcontrol-p)))
  (cond ((vl-delaycontrol-p x) (vl-jp-delaycontrol x))
        ((vl-eventcontrol-p x) (vl-jp-eventcontrol x))
        (t                     (vl-jp-repeateventcontrol x))))

(add-json-encoder vl-delayoreventcontrol-p vl-jp-delayoreventcontrol)

(define vl-jp-maybe-delayoreventcontrol ((x vl-maybe-delayoreventcontrol-p)
                                         &key (ps 'ps))
  (if x
      (vl-jp-delayoreventcontrol x)
    (vl-print "null")))

(add-json-encoder vl-maybe-delayoreventcontrol-p vl-jp-maybe-delayoreventcontrol)




(defines vl-jp-stmt

 (define vl-jp-stmt ((x vl-stmt-p) &key (ps 'ps))
   :measure (two-nats-measure (vl-stmt-count x) 0)
   (b* ((kind (vl-stmt-kind x)))
     (vl-stmt-case x

       :vl-nullstmt
       (jp-object :tag (jp-sym kind)
                  :atts (vl-jp-atts x.atts))

       :vl-assignstmt
       (jp-object :tag    (jp-sym kind)
                  :lvalue (vl-jp-expr x.lvalue)
                  :expr   (vl-jp-expr x.expr)
                  :ctrl   (vl-jp-maybe-delayoreventcontrol x.ctrl)
                  :atts   (vl-jp-atts x.atts))

       :vl-deassignstmt
       (jp-object :tag    (jp-sym kind)
                  :lvalue (vl-jp-expr x.lvalue)
                  :atts   (vl-jp-atts x.atts))

       :vl-enablestmt
       (jp-object :tag    (jp-sym kind)
                  :id     (vl-jp-expr x.id)
                  :args   (vl-jp-exprlist x.args)
                  :atts   (vl-jp-atts x.atts))

       :vl-disablestmt
       (jp-object :tag    (jp-sym kind)
                  :id     (vl-jp-expr x.id)
                  :atts   (vl-jp-atts x.atts))

       :vl-returnstmt
       (jp-object :tag    (jp-sym kind)
                  :atts   (vl-jp-atts x.atts)
                  :val    (vl-jp-maybe-expr x.val))

       :vl-eventtriggerstmt
       (jp-object :tag    (jp-sym kind)
                  :id     (vl-jp-expr x.id)
                  :atts   (vl-jp-atts x.atts))

       :vl-casestmt
       (jp-object :tag      (jp-sym kind)
                  :casetype (vl-jp-casetype x.casetype)
                  :check    (vl-jp-casecheck x.check)
                  :test     (vl-jp-expr x.test)
                  :default  (vl-jp-stmt x.default)
                  :caselist (vl-jp-cases x.caselist)
                  :atts     (vl-jp-atts x.atts))

       :vl-ifstmt
       (jp-object :tag         (jp-sym kind)
                  :condition   (vl-jp-expr x.condition)
                  :truebranch  (vl-jp-stmt x.truebranch)
                  :falsebranch (vl-jp-stmt x.falsebranch)
                  :atts        (vl-jp-atts x.atts))

       :vl-foreverstmt
       (jp-object :tag       (jp-sym kind)
                  :body      (vl-jp-stmt x.body)
                  :atts      (vl-jp-atts x.atts))

       :vl-waitstmt
       (jp-object :tag       (jp-sym kind)
                  :condition (vl-jp-expr x.condition)
                  :body      (vl-jp-stmt x.body)
                  :atts      (vl-jp-atts x.atts))

       :vl-whilestmt
       (jp-object :tag       (jp-sym kind)
                  :condition (vl-jp-expr x.condition)
                  :body      (vl-jp-stmt x.body)
                  :atts      (vl-jp-atts x.atts))

       :vl-forstmt
       (jp-object :tag      (jp-sym kind)
                  :initdecls   (vl-jp-vardecllist x.initdecls)
                  :initassigns (vl-jp-stmtlist x.initassigns)
                  :test        (vl-jp-expr x.test)
                  :stepforms   (vl-jp-stmtlist x.stepforms)
                  :body        (vl-jp-stmt x.body)
                  :atts        (vl-jp-atts x.atts))

       :vl-blockstmt
       (jp-object :tag        (jp-sym kind)
                  :sequential (jp-bool x.sequentialp)
                  :name       (jp-maybe-string x.name)
                  :imports    (vl-jp-importlist x.imports)
                  :paramdecls (vl-jp-paramdecllist x.paramdecls)
                  :vardecls   (vl-jp-vardecllist x.vardecls)
                  :stmts      (vl-jp-stmtlist x.stmts)
                  :atts       (vl-jp-atts x.atts))

       :vl-repeatstmt
       (jp-object :tag       (jp-sym kind)
                  :condition (vl-jp-expr x.condition)
                  :body      (vl-jp-stmt x.body)
                  :atts      (vl-jp-atts x.atts))

       :vl-timingstmt
       (jp-object :tag  (jp-sym kind)
                  :ctrl (vl-jp-delayoreventcontrol x.ctrl)
                  :body (vl-jp-stmt x.body)
                  :atts (vl-jp-atts x.atts))

       )))

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

 (define vl-jp-cases ((x vl-caselist-p) &key (ps 'ps))
   ;; Print the stmtessions as a JSON array with brackets.
   :measure (two-nats-measure (vl-caselist-count x) 1)
   (vl-ps-seq (vl-print "[")
              (vl-jp-cases-aux x)
              (vl-println? "]")))

 (define vl-jp-cases-aux ((x vl-caselist-p) &key (ps 'ps))
   ;; Print the stmtessions as a JSON array with brackets.
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
                (vl-jp-cases-aux (cdr x))))))

(add-json-encoder vl-stmt-p vl-jp-stmt)
(add-json-encoder vl-stmtlist-p vl-jp-stmtlist)
(add-json-encoder vl-caselist-p vl-jp-cases)


(def-vl-jp-aggregate always)
(def-vl-jp-list always :newlines 4)

(def-vl-jp-aggregate initial)
(def-vl-jp-list initial :newlines 4)

(def-vl-jp-aggregate portdecl)
(def-vl-jp-list portdecl :newlines 4)

(def-vl-jp-aggregate fundecl :omit (blockitems))
(def-vl-jp-list fundecl :newlines 4)

(def-vl-jp-aggregate taskdecl :omit (blockitems))
(def-vl-jp-list taskdecl :newlines 4)

(def-vl-jp-aggregate assign)
(def-vl-jp-list assign :newlines 4)



(define vl-jp-warning ((x vl-warning-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Special, custom JSON encoder for warnings."

  :long "<p>We probably don't want to use the ordinary aggregate-encoding stuff
to print @(see vl-warning-p) objects, since the types in the @(':args') field
are dynamic and, besides, who wants to reimplement @(see vl-cw) in other
languages.  Instead, it's probably more convenient to just go ahead and convert
the warning into a printed message here.  We'll include both HTML and plain
TEXT versions of the message.</p>"

  (b* (((vl-warning x) x)
       (text (with-local-ps (vl-cw-obj x.msg x.args)))
       (html (with-local-ps
               (vl-ps-update-htmlp t)
               ;; For the module browser, the warnings get word wrapped by the
               ;; browser anyway, so don't try to wrap them ourselves or things
               ;; get weird looking.
               (vl-ps-update-autowrap-col 100000)
               (vl-cw-obj x.msg x.args))))
    (jp-object :tag    (vl-print "\"warning\"")
               :fatalp (jp-bool x.fatalp)
               :type   (jp-str (symbol-name x.type))
               :fn     (jp-str (symbol-name x.fn))
               :text   (jp-str text)
               :html   (jp-str html))))

(add-json-encoder vl-warning-p jp-warning)

(def-vl-jp-list warning :newlines 4)




(define vl-jp-commentmap-aux ((x vl-commentmap-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps))
    (vl-ps-seq (vl-print "{\"loc\": ")
               (vl-jp-location (caar x))
               (vl-println? ", \"comment\": ")
               (jp-str (cdar x))
               (vl-print "}")
               (if (atom (cdr x))
                   ps
                 (vl-println? ", "))
               (vl-jp-commentmap-aux (cdr x)))))

(define vl-jp-commentmap ((x vl-commentmap-p) &key (ps 'ps))
  (vl-ps-seq (vl-print "[")
             (vl-jp-commentmap-aux x)
             (vl-println? "]")))

(add-json-encoder vl-commentmap-p vl-jp-commentmap)

(def-vl-jp-aggregate modport-port)
(def-vl-jp-list modport-port)
(def-vl-jp-aggregate modport)
(def-vl-jp-aggregate alias)
(def-vl-jp-list alias)

(define vl-jp-fwdtypedefkind ((x vl-fwdtypedefkind-p) &key (ps 'ps))
  (jp-str (case x
            (:vl-enum "enum")
            (:vl-struct "struct")
            (:vl-union "union")
            (:vl-class "class")
            (:vl-interfaceclass "interfaceclass")))
  ///
  (add-json-encoder vl-fwdtypedefkind-p vl-jp-fwdtypedefkind))

(def-vl-jp-aggregate fwdtypedef)

(def-vl-jp-aggregate genvar)
(def-vl-jp-list genvar)

(define vl-jp-modelement ((x vl-modelement-p) &key (ps 'ps))
  :guard-hints (("goal" :in-theory (enable vl-modelement-p)))
  (case (tag x)
    (:VL-interfacePORT (VL-jp-interfacePORT X))
    (:VL-regularPORT (VL-jp-regularPORT X))
    (:VL-PORTDECL (VL-jp-PORTDECL X))
    (:VL-ASSIGN (VL-jp-ASSIGN X))
    (:VL-ALIAS (VL-jp-ALIAS X))
    (:VL-VARDECL (VL-jp-VARDECL X))
    (:VL-PARAMDECL (VL-jp-PARAMDECL X))
    (:VL-FUNDECL (VL-jp-FUNDECL X))
    (:VL-TASKDECL (VL-jp-TASKDECL X))
    (:VL-MODINST (VL-jp-MODINST X))
    (:VL-GATEINST (VL-jp-GATEINST X))
    (:VL-ALWAYS (VL-jp-ALWAYS X))
    (:VL-INITIAL (VL-jp-INITIAL X))
    ;; BOZO implement typedef
    (:VL-TYPEDEF ps)
    (:VL-IMPORT (VL-jp-IMPORT X))
    (:VL-FWDTYPEDEF (VL-jp-FWDTYPEDEF X))
    ;; BOZO implement genvar
    (:VL-GENVAR (vl-jp-genvar x))
    (OTHERWISE (VL-jp-MODPORT X))))

(def-vl-jp-list modelement)

(define vl-jp-genelement ((x vl-genelement-p) &key (ps 'ps))
  (vl-genelement-case x
    :vl-genbase (vl-jp-modelement x.item)
  ;; BOZO implement generates
    :otherwise ps)
  ///
  (add-json-encoder vl-genelement-p vl-jp-genelement))

(def-vl-jp-list genelement)

(def-vl-jp-aggregate module
  :omit (params esim)
  :newlines 2)

(def-vl-jp-list module
  :newlines 1)

(define vl-jp-modalist-aux ((x vl-modalist-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps))
    (vl-ps-seq (jp-str (caar x))
               (vl-print ": ")
               (vl-jp-module (cdar x))
               (if (atom (cdr x))
                   ps
                 (vl-println ", "))
               (vl-jp-modalist-aux (cdr x)))))

(define vl-jp-modalist ((x vl-modalist-p) &key (ps 'ps))
  (vl-ps-seq (vl-print "{")
             (vl-jp-modalist-aux x)
             (vl-println "}")))


(define vl-jp-individual-modules ((x vl-modulelist-p) &key (ps 'ps))
  ;; This doesn't print a single valid JSON object.  Instead, it prints a whole
  ;; list of JSON objects separated by newlines.
  (if (atom x)
      ps
    (vl-ps-seq (vl-jp-module (car x))
               (vl-print "

")
               (vl-jp-individual-modules (cdr x)))))
