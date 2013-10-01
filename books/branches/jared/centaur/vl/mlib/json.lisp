; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "fmt")
(include-book "find-module")
(include-book "centaur/bridge/to-json" :dir :system)
(local (include-book "../util/arithmetic"))


(defsection json-printing
  :parents (printer)
  :short "Routines for encoding various ACL2 structures into <a
href='http://www.json.org/'>JSON</a> format."

  :long "<p>This is a collection of printing routines for translating ACL2
structures into JSON format.  These routines are mainly meant to make it easy
to convert @(see vl) @(see modules) into nice JSON data, but are somewhat
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
                    :in-theory (enable bridge::json-encode-chars
                                       bridge::json-encode-char
                                       bridge::json-encode-weird-char)))))))

(add-json-encoder stringp jp-str)

(define jp-maybe-string ((x vl-maybe-string-p) &key (ps 'ps))
  :parents (json-encoders)
  (if x
      (jp-str x)
    (vl-print "null")))

(add-json-encoder vl-maybe-string-p jp-maybe-string)



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

(define jp-maybe-nat ((x vl-maybe-natp) &key (ps 'ps))
  :parents (json-encoders)
  (if x
      (jp-nat x)
    (vl-print-str "null")))

(add-json-encoder natp jp-nat)
(add-json-encoder posp jp-nat)
(add-json-encoder vl-maybe-natp jp-maybe-nat)
(add-json-encoder vl-maybe-posp jp-maybe-nat)



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



; Fancy automatic json encoding of cutil structures

(program)

(define make-json-encoder-alist
  (efields   ;; A proper cutil::formallist-p for this structure's fields
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

(define def-vl-jp-aggregate-fn (type omit overrides long newlines world)
  (b* ((mksym-package-symbol 'vl::foo)
       (elem-print     (mksym 'vl-jp- type))
       (elem           (mksym 'vl- type))
       (elem-p         (mksym 'vl- type '-p))
       (elem-p-str     (symbol-name elem-p))

       ((std::agginfo agg) (std::get-aggregate elem world))
       ((unless (std::formallist-p agg.efields))
        (raise "Expected :efields for ~x0 to be a valid formallist, found ~x1."
               elem agg.efields))
       (enc-alist (make-json-encoder-alist agg.efields omit overrides world))
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
        (jp-sym ,agg.tag)
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
  (declare (xargs :guard (vl-maybe-natp newlines)))
  `(make-event
    (let ((form (def-vl-jp-aggregate-fn ',type ',omit ',override ',long ',newlines
                  (w state))))
      (value form))))

(logic)


(defmacro def-vl-jp-list (type &key newlines)
  (declare (xargs :guard (vl-maybe-natp newlines)))
  (b* ((mksym-package-symbol 'vl::foo)
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

(define vl-jp-casetype ((x vl-casetype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-netdecltype ((x vl-netdecltype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-taskporttype ((x vl-taskporttype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-vardecltype ((x vl-vardecltype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-paramdecltype ((x vl-paramdecltype-p) &key (ps 'ps))
  :parents (json-encoders)
  :inline t
  (jp-sym x))

(define vl-jp-compoundstmttype ((x vl-compoundstmttype-p) &key (ps 'ps))
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
(add-json-encoder vl-netdecltype-p      vl-jp-netdecltype)
(add-json-encoder vl-taskporttype-p     vl-jp-taskporttype)
(add-json-encoder vl-vardecltype-p      vl-jp-vardecltype)
(add-json-encoder vl-paramdecltype-p    vl-jp-paramdecltype)
(add-json-encoder vl-compoundstmttype-p vl-jp-compoundstmttype)


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

(define jp-bitlist ((x vl-bitlist-p) &key (ps 'ps))
  :parents (json-encoders)
  :short "Encode a @(see vl-bitlist-p) as a JSON string."
  (jp-str (vl-bitlist->string x)))

(add-json-encoder vl-bitlist-p jp-bitlist)

(def-vl-jp-aggregate weirdint)
(def-vl-jp-aggregate string)
(def-vl-jp-aggregate real)
(def-vl-jp-aggregate id)
(def-vl-jp-aggregate hidpiece)
(def-vl-jp-aggregate sysfunname)
(def-vl-jp-aggregate funname)

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
    (otherwise      (vl-jp-sysfunname x))))

(add-json-encoder vl-atomguts-p vl-jp-atomguts)

(def-vl-jp-aggregate atom)

(defsection vl-jp-expr
  :parents (json-encoders)

  (defmacro vl-jp-expr (x &key (ps 'ps))
    `(vl-jp-expr-fn ,x ,ps))

  (defmacro vl-jp-atts (x &key (ps 'ps))
    `(vl-jp-atts-fn ,x ,ps))

  (defmacro vl-jp-atts-aux (x &key (ps 'ps))
    `(vl-jp-atts-aux-fn ,x ,ps))

  (defmacro vl-jp-exprlist (x &key (ps 'ps))
    `(vl-jp-exprlist-fn ,x ,ps))

  (defmacro vl-jp-exprlist-aux (x &key (ps 'ps))
    `(vl-jp-exprlist-aux-fn ,x ,ps))

  (mutual-recursion
   (defund vl-jp-expr-fn (x ps)
     (declare (xargs :guard (vl-expr-p x)
                     :stobjs ps
                     :measure (two-nats-measure (acl2-count x) 2)))
     (b* (((when (vl-fast-atom-p x))
           (vl-jp-atom x))
          ((vl-nonatom x) x))
       (jp-object :tag        (jp-sym :vl-nonatom)
                  :atts       (vl-jp-atts x.atts)
                  :args       (vl-jp-exprlist x.args)
                  :finalwidth (jp-maybe-nat x.finalwidth)
                  :finaltype  (vl-jp-maybe-exprtype x.finaltype))))

   (defund vl-jp-atts-fn (x ps)
     ;; Atts are a string->maybe-expr alist, so turn them into a JSON object
     ;; binding keys to values...
     (declare (xargs :guard (vl-atts-p x)
                     :stobjs ps
                     :measure (two-nats-measure (acl2-count x) 1)))
     (vl-ps-seq (vl-print "{")
                (vl-jp-atts-aux x)
                (vl-println? "}")))

   (defund vl-jp-atts-aux-fn (x ps)
     (declare (xargs :guard (vl-atts-p x)
                     :stobjs ps
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
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

   (defund vl-jp-exprlist-fn (x ps)
     ;; Print the expressions as a JSON array with brackets.
     (declare (xargs :guard (vl-exprlist-p x)
                     :stobjs ps
                     :measure (two-nats-measure (acl2-count x) 1)))
     (vl-ps-seq (vl-print "[")
                (vl-jp-exprlist-aux x)
                (vl-println? "]")))

   (defund vl-jp-exprlist-aux-fn (x ps)
     (declare (xargs :guard (vl-exprlist-p x)
                     :stobjs ps
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           ps))
       (vl-ps-seq (vl-jp-expr (car x))
                  (if (atom (cdr x))
                      ps
                    (vl-println? ", "))
                  (vl-jp-exprlist-aux (cdr x)))))))

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

(def-vl-jp-aggregate port)
(def-vl-jp-list port :newlines 4)


(def-vl-jp-aggregate gatedelay)

(define vl-jp-maybe-gatedelay ((x vl-maybe-gatedelay-p) &key (ps 'ps))
  :parents (json-encoders vl-maybe-gatedelay-p)
  (if x
      (vl-jp-gatedelay x)
    (vl-print "null")))

(add-json-encoder vl-maybe-gatedelay-p vl-jp-maybe-gatedelay)

(def-vl-jp-aggregate netdecl)
(def-vl-jp-list netdecl :newlines 4)

(def-vl-jp-aggregate regdecl)
(def-vl-jp-list regdecl :newlines 4)

(def-vl-jp-aggregate plainarg)
(def-vl-jp-list plainarg :newlines 4)

(def-vl-jp-aggregate namedarg)
(def-vl-jp-list namedarg :newlines 4)

(def-vl-jp-aggregate vardecl)
(def-vl-jp-list vardecl :newlines 4)

(def-vl-jp-aggregate eventdecl)
(def-vl-jp-list eventdecl :newlines 4)

(def-vl-jp-aggregate paramdecl)
(def-vl-jp-list paramdecl :newlines 4)

(define vl-jp-blockitem ((x vl-blockitem-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-blockitem-p)))
  (mbe :logic
       (cond ((vl-regdecl-p x)    (vl-jp-regdecl x))
             ((vl-vardecl-p x)    (vl-jp-vardecl x))
             ((vl-eventdecl-p x)  (vl-jp-eventdecl x))
             (t                   (vl-jp-paramdecl x)))
       :exec
       (case (tag x)
         (:vl-regdecl   (vl-jp-regdecl x))
         (:vl-vardecl   (vl-jp-vardecl x))
         (:vl-eventdecl (vl-jp-eventdecl x))
         (otherwise     (vl-jp-paramdecl x)))))

(add-json-encoder vl-blockitem-p vl-jp-blockitem)
(def-vl-jp-list blockitem)

(define vl-jp-arguments ((x vl-arguments-p) &key (ps 'ps))
  :parents (json-encoders vl-arguments-p)
  (b* (((vl-arguments x) x))
    (jp-object :tag    (jp-sym :vl-arguments)
               :namedp (jp-bool x.namedp)
               :args   (if x.namedp
                           (vl-jp-namedarglist x.args)
                         (vl-jp-plainarglist x.args)))))

(add-json-encoder vl-arguments-p vl-jp-arguments)

(def-vl-jp-aggregate gatestrength)

(define vl-jp-maybe-gatestrength ((x vl-maybe-gatestrength-p) &key (ps 'ps))
  (if x
      (vl-jp-gatestrength x)
    (vl-print "null")))

(add-json-encoder vl-maybe-gatestrength-p vl-jp-maybe-gatestrength)

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

(def-vl-jp-aggregate assignstmt)
(def-vl-jp-aggregate nullstmt)
(def-vl-jp-aggregate enablestmt)
(def-vl-jp-aggregate deassignstmt)
(def-vl-jp-aggregate disablestmt)
(def-vl-jp-aggregate eventtriggerstmt)

(define vl-jp-atomicstmt ((x vl-atomicstmt-p) &key (ps 'ps))
  :guard-hints (("Goal" :in-theory (enable vl-atomicstmt-p)))
  (mbe :logic
       (cond ((vl-nullstmt-p x)          (vl-jp-nullstmt x))
             ((vl-assignstmt-p x)        (vl-jp-assignstmt x))
             ((vl-deassignstmt-p x)      (vl-jp-deassignstmt x))
             ((vl-enablestmt-p x)        (vl-jp-enablestmt x))
             ((vl-disablestmt-p x)       (vl-jp-disablestmt x))
             (t                          (vl-jp-eventtriggerstmt x)))
       :exec
       (case (tag x)
         (:vl-nullstmt           (vl-jp-nullstmt x))
         (:vl-assignstmt         (vl-jp-assignstmt x))
         (:vl-deassignstmt       (vl-jp-deassignstmt x))
         (:vl-enablestmt         (vl-jp-enablestmt x))
         (:vl-disablestmt        (vl-jp-disablestmt x))
         (otherwise              (vl-jp-eventtriggerstmt x)))))


(defmacro vl-jp-stmt (x)
  `(vl-jp-stmt-fn ,x ps))

(defmacro vl-jp-stmtlist (x)
  `(vl-jp-stmtlist-fn ,x ps))

(defmacro vl-jp-stmtlist-aux (x)
  `(vl-jp-stmtlist-aux-fn ,x ps))

(mutual-recursion

 (defund vl-jp-stmt-fn (x ps)
   (declare (xargs :guard (vl-stmt-p x)
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 2)))
   (b* (((when (vl-fast-atomicstmt-p x))
         (vl-jp-atomicstmt x))
        ((vl-compoundstmt x) x))
     (jp-object :tag         (jp-sym :vl-compoundstmt)
                :type        (vl-jp-compoundstmttype x.type)
                :exprs       (vl-jp-exprlist x.exprs)
                :stmts       (vl-jp-stmtlist x.stmts)
                :name        (jp-maybe-string x.name)
                :decls       (vl-jp-blockitemlist x.decls)
                :ctrl        (vl-jp-maybe-delayoreventcontrol x.ctrl)
                :sequentialp (jp-bool x.sequentialp)
                :casetype    (vl-jp-casetype x.casetype)
                :atts        (vl-jp-atts x.atts))))

 (defund vl-jp-stmtlist-fn (x ps)
   ;; Print the stmtessions as a JSON array with brackets.
   (declare (xargs :guard (vl-stmtlist-p x)
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 1)))
   (vl-ps-seq (vl-print "[")
              (vl-jp-stmtlist-aux x)
              (vl-println? "]")))

 (defund vl-jp-stmtlist-aux-fn (x ps)
   (declare (xargs :guard (vl-stmtlist-p x)
                   :stobjs ps
                   :measure (two-nats-measure (acl2-count x) 0)))
   (b* (((when (atom x))
         ps))
     (vl-ps-seq (vl-jp-stmt (car x))
                (if (atom (cdr x))
                    ps
                  (vl-println? ", "))
                (vl-jp-stmtlist-aux (cdr x))))))

(add-json-encoder vl-stmt-p vl-jp-stmt)
(add-json-encoder vl-stmtlist-p vl-jp-stmtlist)


(def-vl-jp-aggregate always)
(def-vl-jp-list always :newlines 4)

(def-vl-jp-aggregate initial)
(def-vl-jp-list initial :newlines 4)

(def-vl-jp-aggregate taskport)
(def-vl-jp-list taskport :newlines 4)

(def-vl-jp-aggregate fundecl)
(def-vl-jp-list fundecl :newlines 4)

(def-vl-jp-aggregate taskdecl)
(def-vl-jp-list taskdecl :newlines 4)

(def-vl-jp-aggregate portdecl)
(def-vl-jp-list portdecl :newlines 4)

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
       (html (with-local-ps (vl-ps-update-htmlp t)
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
