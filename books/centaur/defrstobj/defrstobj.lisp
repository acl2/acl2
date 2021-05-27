; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
; Shilpi Goel <shilpi@centtech.com>: added support for optional universal
;                                    accessor and updater functions

; (depends-on "build/defrec-certdeps/DEFSTOBJ-FIELD-TEMPLATE.certdep" :dir :system)
; (depends-on "build/defrec-certdeps/DEFSTOBJ-TEMPLATE.certdep" :dir :system)

(in-package "RSTOBJ")
(include-book "def-typed-record")
(include-book "generic")
(include-book "misc/records" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/lists/nth" :dir :system)
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/lists/len" :dir :system)


(defsection defrstobj
  :parents (stobj macro-libraries)
  :short "Record-like @(see stobj)s combine the run-time efficiency of stobjs
with the reasoning efficiency of records.  They are designed for modeling,
e.g., the state of a processor or virtual machine."

  :long "<h3>Introduction</h3>

<p>A <b>Record-like @(see stobj)</b> (\"rstobj\") is a way to model a
processor's state that allows for both good execution efficiency and good
reasoning efficiency.</p>

<p>The state is implemented as a stobj so that it can be accessed efficiently
and updated destructively, without, e.g., lots of consing just to build the new
state object.  This is good since it's useful for processor models to execute
efficiently.</p>

<p>The state is reasoned about as if it were a \"record,\" in the sense of the
@('misc/records') book.  The top-level field accessors and updators of the
stobj are (logically) defined as @('g') and @('s').  This style of reasoning
seems good.  It has been used in the compositional cutpoint techniques
developed by John Matthews, J Moore, Sandip Ray, and Daron Vroon, the
\"wormhole abstraction\" of Dave Greve at Rockwell Collins, the work of Eric
Smith for automated cutpoint-based proofs, etc.  There are probably other
people who are also using records, e.g., Rob Sumners.</p>


<h3>Using @('defrstobj')</h3>

<p>The syntax of @('defrstobj') is nearly that of defstobj, except that:</p>

<ul>

<li>Simply typed (non-array) fields require an additional @(':fix') argument
that says how to coerce \"bad\" objects into an object of the appropriate type.
This should be a term mentioning @('acl2::x').</li>

<li>Array fields require an additional @(':typed-record') argument that names
recognizer function for a typed record; see @(see def-typed-record).</li>

<li>Optionally, you can have @('defrstobj') define a universal
accessor and a universal updater function using keywords
@(':accessor') and @(':updater') respectively.  These functions can
come in handy when using
@('[books]/std/stobjs/updater-independence').</li>

</ul>

<p>Example:</p>

@({
    (include-book \"centaur/defrstobj/defrstobj\" :dir :system)

    (defrstobj st

      (regs :type (array (unsigned-byte 64) (32))
            :initially 0
            :typed-record u32-tr-p)

      (pc   :type (unsigned-byte 64)
            :initially 0
            :fix (unsigned-byte-fix 64 x))

      (mem  :type (array (unsigned-byte 8) (*mem-size*))
            :initially 0
            :typed-record u8-tr-p)

      :inline t
      ;; [Optional] Universal accessor and updater functions
      :accessor sr
      :updater sw)
})

<p>See also @('centaur/defrstobj/basic-tests.lisp') for several more examples,
including examples of how to use @('def-typed-record').</p>

<h4>Working with Universal Accessor and Updater Functions</h4>

<p>The universal accessor and updater functions have the following
signature:</p>

<code>
(sr field index stobj)       -&gt; value
(sw field index value stobj) -&gt; new-stobj
</code>

<p>where @('field') is a keyword corresponding to a stobj field (e.g.,
@(':mem') in the above example).  Their definition is pretty straightforward
--- depending on the @('field'), the appropriate accessor/updater (e.g.,
@('get-mem/set-mem')) is called.  However, due to the case-split on @('field'),
these two functions would be expensive for execution, so we've made them
non-executable.</p>

<p>In addition to these two functions, we also provide top-level field
accessors and updaters (e.g., @('@mem/!mem') for the @('mem') field above)
which have an @(see acl2::mbe) --- the @(':logic') definition is in terms of
the universal accessor or updater, and the @(':exec') definition is the stobj
field accessor or updater (e.g., @('get-mem/set-mem')).  These top-level field
accessors and updaters are inlined for execution performance.</p>

<p>We recommend the following strategy when working with the universal accessor
and updater functions.  You probably want all your theorems to be in terms of
the two universal accessor/updater functions.  Keep the top-level field
accessors/updaters enabled --- you probably want to use them in functions you
define on top of the stobj so that you get the performance of the underlying
concrete stobj while you reason about the universal accessor/updater
functions.</p>

<p>In addition to facilitating use with
@('stobjs::stobj-updater-independence'), a benefit of this strategy is
that it can reduce the term size during reasoning.  E.g., writing
@('v') to the @('i')th location of the @('mem') field using
@('set-mem') (which is enabled by default) would look like the
following:</p>

<code>
(s :mem (u8-tr-set i v (g :mem st)) st)
</code>

<p>When using the universal accessor/updater functions, it'll look like the
following:</p>

<code>
(sw :mem i v st)
</code>

<h3>Notes</h3>

<p>Record-like stobjs are now based on abstract stobjs.  This offers various
benefits over a <see topic='@(url legacy-defrstobj)'>previous version</see> of
rstobjs that didn't use abstract stobjs.  For instance, you no longer need any
kind of good-stobj predicate, and the top-level logical story is now just in
terms of @('g') and @('s') instead of stobj-specific functions.</p>

<p>A subtlety of treating the state as a record is that you (logically)
\"lose\" any type information about the top-level fields.  For instance, you
would expect to know that the @('pc') field above is a 64-bit natural.</p>

<p>With rstobjs, the state is logically just a record, so logically there is no
restriction on the @('pc').  However, the executable accessor for the @('pc')
will logically be defined as, e.g.,</p>

@({
    (unsigned-byte-fix 64 (g :pc st))
})

<p>Note that this fixing is free in the execution; the abstract stobj invariant
allows us to assume that @('pc') is well-formed so we don't need to do any
fixing.</p>

<p>Arrays complicate things.  If a stobj only has non-array fields, then
viewing it as a record is pretty straightforward&mdash;we basically have a key
corresponding to each field.  But how do we handle array fields, which have
their own collections of elements?</p>

<p>One approach might be to try to keep viewing the stobj as a flat record.
For instance, we might try to have the story be something like <i>arr[3]
corresponds to the field (:ARR . 3)</i> or similar.  This is probably possible,
but something I didn't like about it was that it means we would also lose the
type information on the array elements.</p>

<p>Instead, I set things up so that the whole array looks like just one field
in the stobj.  The array itself is represented as a typed record, with its own
get/set functions that satisfy the theorems of Greve and Wilding's typed
records book.  See @(see def-typed-record).</p>")

; I originally imagined that DEFRSTOBJ would automatically introduce the typed
; records needed to support each field (and even got pretty far along with the
; implementation of this idea).  But the problem with this is that:
;
;   (1) it makes DEFRSTOBJ really complicated, having to deal with things like
;       comprehending type specifiers and manage the generation of a lot more
;       functions, etc., which further complicates getting the theory right,
;       and
;
;   (2) it seems like the user really needs to know about the typed records he
;       is introducing anyway, e.g., for the stobj above you have to modify the
;       memory using u8-tr-set and the registers with u32-tr-set, etc., so we
;       might as well give him full control over the definition of his typed
;       records and how he wants to share them between different kinds of
;       fields.
;
; This seems like a good decision that makes DEFRSTOBJ much simpler.

(program)

; An RSF ("rstobj field") is like an ordinary stobj field, but can have the
; additional :typed-record argument.

(defun eat-typed-record (rsf)
  ;; Remove the :typed-record part to get a normal STOBJ field.
  (b* (((unless (and (true-listp rsf)
                     (symbolp (car rsf))
                     (keyword-value-listp (cdr rsf))))
        (er hard? 'make-normal-stobj-field
            "Malformed rstobj field: ~x0.~%" rsf)))
    (cons (car rsf)
          (remove-keyword :fix (remove-keyword :typed-record (cdr rsf))))))

(defun eat-typed-records (rsfs)
  (if (atom rsfs)
      nil
    (cons (eat-typed-record (car rsfs))
          (eat-typed-records (cdr rsfs)))))

(defun tr-alist (rsfs)
  ;; Build an alist binding every field name to its :typed-record entry (or
  ;; NIL).  Note: we rely on this binding every field, even if it has no
  ;; :typed-record part or isn't even an array field.
  (b* (((when (atom rsfs))
        nil)
       (rsf  (car rsfs))
       (name (car rsf))
       (look (assoc-keyword :typed-record (cdr rsf))))
    (cons (cons name (second look))
          (tr-alist (cdr rsfs)))))

(defun fix-alist (rsfs)
  ;; Build an alist binding every field name to its :typed-record entry (or
  ;; NIL).  Note: we rely on this binding every field, even if it has no
  ;; :typed-record part or isn't even an array field.
  (b* (((when (atom rsfs))
        nil)
       (rsf  (car rsfs))
       (name (car rsf))
       (look (assoc-keyword :fix (cdr rsf))))
    (cons (cons name (second look))
          (fix-alist (cdr rsfs)))))


(defun make-$c-fields (st-fields mksym-pkg)
  (if (atom st-fields)
      nil
    (cons (cons (mksym (caar st-fields) '$c)
                (cdar st-fields))
          (make-$c-fields (cdr st-fields) mksym-pkg))))


; An FTA ("field template alist") is an alist that is similar to ACL2's notion
; of a defstobj-template, except that
;
;   (1) instead of being an 8-tuple whose format has to be remembered, it is
;       just an alist with named keys, and
;
;   (2) we extend it with the :typed-record field, etc.


(defmacro access-defstobj-field-template (x field)
  `(acl2::access acl2::defstobj-field-template ,x ,field))

(defun destructure-defstobj-field-template (x)

  ;; BOZO this has to be kept in sync with defstobj-field-template.

  (let ((fieldp-name (access-defstobj-field-template x :fieldp-name))
        (type (access-defstobj-field-template x :type))
        (init (access-defstobj-field-template x :init))
        (accessor-name (access-defstobj-field-template x :accessor-name))
        (updater-name (access-defstobj-field-template x :updater-name))
        (length-name (access-defstobj-field-template x :length-name))
        (resize-name (access-defstobj-field-template x :resize-name))
        (resizable (access-defstobj-field-template x :resizable))
        (other (access-defstobj-field-template x :other)))
    (list fieldp-name type init accessor-name updater-name length-name
          resize-name resizable other)))

(defun make-fta (field-name typed-rec fix defstobj-fld-template mksym-pkg tr-table)
  (declare (xargs :mode :program))
  (b* (((list recog-name type init accessor-name updater-name length-name
              resize-name resizable other)
        ;; BOZO this has to be kept in sync with defstobj-field-template
        (destructure-defstobj-field-template defstobj-fld-template))


       ;; We could just override the init settting with the typed-record init
       ;; value, but we can't tell the difference here between one where no
       ;; :initially key was given and one where :initially nil was given.  For
       ;; now we'll just say the :initially value has to be specified and equal
       ;; to the typed record default.
       (- (b* (((unless typed-rec) t)
               (tr-entry (cdr (assoc typed-rec tr-table)))
               ((unless tr-entry)
                (er hard? 'make-fta
                    "Field ~x0 is supposed to be a ~x1 typed record, but this ~
                     doesn't appear to be a typed record: it must have an ~
                     entry in the ~x2 table.  (Typically the name ends in ~
                     -TR-P.)"
                    field-name typed-rec 'typed-records))
               (tr-fi-pairs (cdr (assoc :fi-pairs tr-entry)))
               (default-lambda (cadr (assoc 'elem-default tr-fi-pairs)))
               (default-val (third default-lambda))) ;; (lambda () 0), e.g.
            (or (equal init default-val)
                (er hard? 'check-fta-init-vals
                    "Field ~x0 is a ~x1 record, which has default value ~x2, ~
                     but its initial value is ~x3 -- they must be the same."
                    field-name
                    typed-rec
                    default-val
                    init))))

       (field-key (intern (symbol-name field-name) "KEYWORD"))
       (size-key (and typed-rec
                      (intern
                       (concatenate 'string (symbol-name field-name) "-SIZE")
                       "KEYWORD")))

       (- (or (and length-name
                   typed-rec)
              (and (not length-name)
                   (not typed-rec))
              (er hard? 'make-fta
                  "Field ~x0 is not allowed; each array needs to have a ~
                   :typed-record entry, and non-arrays may not have ~
                   :typed-record entries." field-name)))

       (- (and fix typed-rec
               (er hard? 'make-fta
                   "Field ~x0 is not allowed: only non-array fields may specify :fix.")))

       (- (and (not typed-rec) (not fix)
               (not (equal type t))
               (er hard? 'make-fta
                   "Scalar field ~x0 must have a :fix argument since it has a ~
                    nontrivial type ~x1.~%"
                   field-name type))))

    `((:field-name    . ,field-name)
      (:recog-name$c    . ,recog-name)
      (:type          . ,type)
      (:init          . ,init)
      (:accessor-name$c . ,accessor-name)
      (:updater-name$c  . ,updater-name)
      (:length-name$c   . ,length-name)
      (:resize-name$c   . ,resize-name)
      (:resizable     . ,resizable)
      (:other         . ,other)
      (:offset        . ,(acl2::defconst-name accessor-name))
      (:typed-record  . ,typed-rec)
      (:accessor-name . ,(mksym 'get- field-name))
      (:updater-name  . ,(mksym 'set- field-name))
      (:length-name   . ,(and typed-rec (mksym field-name '-length)))
      (:grow-name     . ,(and resizable (mksym 'grow- field-name)))
      (:empty-name    . ,(and resizable (mksym 'empty- field-name)))
      (:field-key     . ,field-key)
      (:size-key      . ,size-key)
      (:fix           . ,fix))))

(defun make-ftas (tr-alist st-fld-templates fix-alist mksym-pkg tr-table)
  (if (atom tr-alist)
      nil
    (cons (make-fta (caar tr-alist) ;; field name
                    (cdar tr-alist) ;; typed-rec
                    (cdar fix-alist) ;; fix
                    (car st-fld-templates)
                    mksym-pkg tr-table)
          (make-ftas (cdr tr-alist) (cdr st-fld-templates) (cdr fix-alist) mksym-pkg tr-table))))


(defun additional-exec-defs (name$c ftas mksym-pkg)
  (b* (((when (atom ftas)) nil)
       (rest (additional-exec-defs name$c (cdr ftas) mksym-pkg))
       (fta (car ftas))
       (resizable (cdr (assoc :resizable fta)))
       ((unless resizable) rest)
       (empty (cdr (assoc :empty-name fta)))
       (empty$c (mksym empty '$c))
       (resize (cdr (assoc :resize-name$c fta))))
    (cons `(defun ,empty$c (,name$c)
             (declare (xargs :stobjs ,name$c))
             (,resize 0 ,name$c))
          rest)))

(defun creator-logic-updates (ftas)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas)) nil)
       (rest (creator-logic-updates (cdr ftas)))
       (fta (car ftas))
       (size (cdr (assoc :size-key fta)))
       (field (cdr (assoc :field-key fta)))
       ((unless size) ;; scalar
        (b* ((init (cdr (assoc :init fta))))
          (cons `(x (s ,field (quote ,init) x)) rest)))
       (type (cdr (assoc :type fta)))
       (init-size (car (third type)))
       (- (or (natp init-size)
              (er hard? 'creator-logic-updates
                  "Couldn't find array initial size in type decl ~x0 for field ~x1"
                  type (cdr (assoc :field-name fta))))))
    (append `((x (s ,field nil x))
              (x (s ,size ,init-size x)))
            rest)))



(defun scalar-fixing-function-thms (ftas w mksym-pkg)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas)) nil)
       (rest (scalar-fixing-function-thms (cdr ftas) w mksym-pkg))
       (fta (car ftas))
       (fix (cdr (assoc :fix fta)))
       ((unless fix) rest)
       (field (cdr (assoc :field-name fta)))
       (type (cdr (assoc :type fta)))
       (hyp (translate-declaration-to-guard type 'x w))
       (id-thmname (mksym 'rstobj-fix-idempotent-for field))
       (elemp-thmname (mksym 'rstobj-fix-elem-p-for field)))
    (list* `(defthm ,id-thmname
              (implies ,hyp
                       (equal ,fix x)))
           `(defthm ,elemp-thmname
              ,(translate-declaration-to-guard type fix w))
           rest)))

(defun scalar-fixing-function-thm-names (ftas mksym-pkg)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas)) nil)
       (rest (scalar-fixing-function-thm-names (cdr ftas) mksym-pkg))
       (fta (car ftas))
       (fix (cdr (assoc :fix fta)))
       ((unless fix) rest)
       (field (cdr (assoc :field-name fta))))
    (list* (mksym 'rstobj-fix-idempotent-for field)
           (mksym 'rstobj-fix-elem-p-for field)
           rest)))

(defun collect-typed-rec-theorems (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (collect-typed-rec-theorems (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest))
    (append (cdr (assoc :theorems (cdr (assoc typed-rec tr-table))))
            (collect-typed-rec-theorems (cdr ftas) tr-table))))



(defun logic-field-functions-one (fta w tr-table mksym-pkg)
  (b* ((typed-rec (cdr (assoc :typed-record fta)))
       (acc       (cdr (assoc :accessor-name fta)))
       (upd       (cdr (assoc :updater-name fta)))
       (key       (cdr (assoc :field-key fta)))
       (type      (cdr (assoc :type fta)))
       (acc$a     (mksym acc '$a))
       (upd$a     (mksym upd '$a))

       ((unless typed-rec)
        ;; scalar -- just getter and setter
        (b* ((fix (cdr (assoc :fix fta)))
             (get-core `(g ,key x))
             (get-body (if fix
                           (subst get-core 'x fix)
                         get-core))
             (guard (translate-declaration-to-guard type 'v w)))
          `((defun ,acc$a (x)
              (declare (xargs :guard t))
              ,get-body)
            (defun ,upd$a (v x)
              (declare (xargs :guard ,guard))
              (s ,key v x)))))

       (length    (cdr (assoc :length-name fta)))
       (grow      (cdr (assoc :grow-name fta)))
       (empty     (cdr (assoc :empty-name fta)))

       (length$a  (mksym length '$a))
       (size-key  (cdr (assoc :size-key fta)))

       (grow/empty
        (and grow
             `((defun ,(mksym grow '$a) (n x)
                 (declare (xargs :guard (and (natp n)
                                             (<= (,length$a x) n))))
                 (s ,size-key n x))
               (defun ,(mksym empty '$a) (x)
                 (declare (xargs :guard t))
                 (s ,key nil (s ,size-key 0 x))))))

       (guard (translate-declaration-to-guard (second type) 'v w))

       (fi-pairs (cdr (assoc :fi-pairs
                             (cdr (assoc typed-rec tr-table)))))
       (tr-get (second (assoc 'tr-get fi-pairs)))
       (tr-set (second (assoc 'tr-set fi-pairs))))

    `((defun ,length$a (x)
        (declare (xargs :guard t)
                 ,@(and (not grow) '((ignore x))))
        ,(if grow
             ;; resizable
             `(nfix (g ,size-key x))
           ;; fixed size given by array decl
           (car (third type))))

      (defun ,acc$a (i x)
        (declare (xargs :guard (and (natp i)
                                    (< i (,length$a x)))))
        (,tr-get i (g ,key x)))

      (defun ,upd$a (i v x)
        (declare (xargs :guard (and (natp i)
                                    (< i (,length$a x))
                                    ,guard)))
        (s ,key (,tr-set i v (g ,key x)) x))

      . ,grow/empty)))

(defun logic-field-functions (ftas w tr-table mksym-pkg)
  (if (atom ftas)
      nil
    (append (logic-field-functions-one (car ftas) w tr-table mksym-pkg)
            (logic-field-functions (cdr ftas) w tr-table mksym-pkg))))


(defun make-fieldmap-entries (ftas)
  (b* (((when (atom ftas)) nil)
       (fta (car ftas))
       (field-key (cdr (assoc :field-key fta)))
       (size-key (cdr (assoc :size-key fta))))
    (cons (if size-key
              `(make-array-fieldinfo :tr-key ,field-key :size-key ,size-key)
            `(make-scalar-fieldinfo :key ,field-key))
          (make-fieldmap-entries (cdr ftas)))))

(defun make-tr-get-entries (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (make-tr-get-entries (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (tr-get (second (assoc 'tr-get (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table))))))))
    (cons `(,field-key (,tr-get i tr)) rest)))

(defun make-tr-set-entries (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (make-tr-set-entries (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (tr-set (second (assoc 'tr-set (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table))))))))
    (cons `(,field-key (,tr-set i v tr)) rest)))

(defun make-tr-fix-entries (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (make-tr-fix-entries (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (tr-fix (second (assoc 'elem-fix (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table))))))))
    (cons `(,field-key (,tr-fix v)) rest)))

(defun make-tr-default-entries (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (make-tr-default-entries (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (tr-default (second (assoc 'elem-default (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table))))))))
    (cons `(,field-key (,tr-default)) rest)))

(defun make-tr-elem-p-entries (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (make-tr-elem-p-entries (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (tr-elem-p (second (assoc 'elem-p (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table))))))))
    (cons `(,field-key (,tr-elem-p v)) rest)))

(defun make-scalar-fix-entries (ftas)
  (b* (((when (atom ftas)) nil)
       (rest (make-scalar-fix-entries (cdr ftas)))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((when typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (fix (cdr (assoc :fix fta)))
       (fix-body (if fix `((lambda (x) ,fix) v) 'v)))
    (cons `(,field-key ,fix-body) rest)))

(defun make-scalar-elem-p-entries (ftas wrld)
  (b* (((when (atom ftas)) nil)
       (rest (make-scalar-elem-p-entries (cdr ftas) wrld))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((when typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (type (cdr (assoc :type fta)))
       (form (translate-declaration-to-guard type 'v wrld)))
    (cons `(,field-key ,form) rest)))

(defun make-field-corr-of-tr-key-concls (ftas tr-table)
  (b* (((when (atom ftas)) nil)
       (rest (make-field-corr-of-tr-key-concls (cdr ftas) tr-table))
       (fta (car ftas))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((unless typed-rec) rest)
       (field-key (cdr (assoc :field-key fta)))
       (tr-get (second (assoc 'tr-get (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table))))))))
    (cons `(implies (equal trkey ,field-key)
                    (equal (,tr-get i (g trkey st$a))
                           (if (< i (len (nth idx st$c)))
                               (nth i (nth idx st$c))
                             (rstobj-tmp-tr-default trkey))))
          rest)))

(defun array-types-preserved-thms (ftas w mksym-pkg)
  (b* (((when (atom ftas)) nil)
       (rest (array-types-preserved-thms (cdr ftas) w mksym-pkg))
       (fta (car ftas))
       (type (cdr (assoc :type fta)))
       ((unless (and (consp type) (eq (car type) 'array))) rest)
       (recog (cdr (assoc :recog-name$c fta)))
       (hyp (translate-declaration-to-guard (second type) 'v w)))
    (append
     `((defthm ,(mksym recog '-of-repeat)
         (implies ,hyp
                  (,recog (acl2::repeat n v)))
         :hints(("Goal" :in-theory (enable acl2::repeat)
                 :induct (acl2::repeat n v))))

       (defthm ,(mksym recog '-of-update-nth)
         (implies (and ,hyp
                       (,recog x)
                       (<= (nfix i) (len x)))
                  (,recog (update-nth i v x)))
         :hints(("Goal" :in-theory (enable update-nth len))))

       (defthm ,(mksym recog '-of-resize-list)
         (implies (and ,hyp
                       (,recog x))
                  (,recog (resize-list x n v)))
         :hints(("Goal" :in-theory (enable resize-list)))))
     rest)))


(defun absstobj-exports-one (fta mksym-pkg)
  (b* ((typed-rec (cdr (assoc :typed-record fta)))
       (acc       (cdr (assoc :accessor-name fta)))
       (upd       (cdr (assoc :updater-name fta)))

       (acc$a     (mksym acc '$a))
       (acc$c     (cdr (assoc :accessor-name$c fta)))
       (upd$a     (mksym upd '$a))
       (upd$c     (cdr (assoc :updater-name$c fta)))

       (acc/upd
        `((,acc :logic ,acc$a :exec ,acc$c)
          (,upd :logic ,upd$a :exec ,upd$c)))

       ((unless typed-rec)
        ;; scalar -- just getter and setter
        acc/upd)

       (length    (cdr (assoc :length-name fta)))
       (grow      (cdr (assoc :grow-name fta)))
       (empty     (cdr (assoc :empty-name fta)))

       (length$a  (mksym length '$a))
       (length$c  (cdr (assoc :length-name$c fta)))

       (grow/empty
        (and grow
             `((,grow :logic ,(mksym grow '$a) :exec ,(cdr (assoc :resize-name$c fta)))
               (,empty :logic ,(mksym empty '$a) :exec ,(mksym empty '$c))))))

    `((,length :logic ,length$a :exec ,length$c)
      ,@acc/upd
      . ,grow/empty)))

(defun absstobj-exports (ftas mksym-pkg)
  (if (atom ftas)
      nil
    (append (absstobj-exports-one (car ftas) mksym-pkg)
            (absstobj-exports (cdr ftas) mksym-pkg))))



(defmacro access-defstobj-template (x field)
  `(acl2::access acl2::defstobj-template ,x ,field))

(defun destructure-defstobj-template (x)

  ;; BOZO this has to be kept in sync with defstobj-template.

  (let ((recognizer (access-defstobj-template x :recognizer))
        (creator (access-defstobj-template x :creator))
        (field-templates (access-defstobj-template x :field-templates))
; Matt K. mod: :doc is no longer supported for defstobj after v7-1
        ;; (doc (access-defstobj-template x :doc))
        (inline (access-defstobj-template x :inline))
        (congruent-to (access-defstobj-template x :congruent-to))
        (non-memoizable (access-defstobj-template x :non-memoizable)))
    (list recognizer
          creator
          field-templates
; Matt K. mod: :doc is no longer supported for defstobj after v7-1
          ;; doc
          inline
          congruent-to
          non-memoizable)))

;; [Shilpi] Added support for (optional) top-level accessor/updater functions.

(defun make-val-fixing-fn (ftas tr-table)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas))
        `((otherwise nil)))
       (fta (car ftas))
       (rest (make-val-fixing-fn (cdr ftas) tr-table))
       (field-key (cdr (assoc :field-key fta)))
       (fix (cdr (assoc :fix fta)))
       (typed-rec (cdr (assoc :typed-record fta)))
       ((when (and (not fix) (not typed-rec)))
        ;; Fields of type T.
        (cons `(,field-key x) rest))
       ((when fix) ;; scalar field
        (cons `(,field-key ,fix) rest))
       ((unless typed-rec)
        (er hard? 'make-val-fixing-fn
            "make-val-fixing-fn: Expected a typed record for field: ~x0."
            field-key))
       (tr-fix
        (third ;; Remove (lambda (x) ???) to get just the ??? form.
         (second (assoc 'elem-fix
                        (cdr (assoc :fi-pairs (cdr (assoc typed-rec tr-table)))))))))
    (cons
     `(,field-key ,tr-fix)
     rest)))

(defun top-level-getter-fns (name ftas mksym-pkg)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas))
        `((otherwise nil)))
       (fta (car ftas))
       (rest (top-level-getter-fns name (cdr ftas) mksym-pkg))
       (field-key (cdr (assoc :field-key fta)))
       (accessor (cdr (assoc :accessor-name fta)))
       ((unless (cdr (assoc :size-key fta))) ;; continue if scalar
        (append
         `((,field-key (,accessor ,name)))
         rest))
       (index (mksym 'index)))
    (append
     `((,field-key (,accessor ,index ,name)))
     rest)))

(defun top-level-setter-fns (name ftas mksym-pkg)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas))
        `((otherwise ,name)))
       (fta (car ftas))
       (rest (top-level-setter-fns name (cdr ftas) mksym-pkg))
       (field-key (cdr (assoc :field-key fta)))
       (updater (cdr (assoc :updater-name fta)))
       (value (mksym 'value))
       ((unless (cdr (assoc :size-key fta))) ;; continue if scalar
        (append
         `((,field-key (,updater ,value ,name)))
         rest))
       (index (mksym 'index)))
    (append
     `((,field-key (,updater ,index ,value ,name)))
     rest)))

(defun guards-for-top-level-acc/upd (name setter/getter ftas mksym-pkg w)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas))
        `((otherwise t)))
       (fta (car ftas))
       (rest (guards-for-top-level-acc/upd name setter/getter (cdr ftas) mksym-pkg w))
       (field (cdr (assoc :field-name fta)))
       (type (cdr (assoc-equal :type fta)))
       (field-key (cdr (assoc :field-key fta)))
       (value (mksym 'value))
       ((unless (cdr (assoc :size-key fta))) ;; scalar
        (if (eq setter/getter :setter)
            (b* ((recog (acl2::translate-declaration-to-guard
                         type value w))
                 ((unless (eq type 'T))
                  ;; Fields with type T needn't be considered.
                  (append `((,field-key ,recog)) rest)))
              rest)
          rest))
       ((unless (and (eql (len type) 3)
                     (consp (third type))))
        (er hard? 'guards-for-top-level-acc/upd
            "~% Expected an array declaration for ~p0, but got ~p1 instead."
            field type))
       (value-recog (acl2::translate-declaration-to-guard (second type) value w))
       (len `(,(cdr (assoc :length-name fta)) ,name))
       (index (mksym 'index))
       (index-recog `(and (natp ,index)
                          (< ,index ,len))))
    (if (eq setter/getter :setter)
        (append `((,field-key (and ,value-recog ,index-recog))) rest)
      (append `((,field-key ,index-recog)) rest))))

(defun mbe-accessor/updater-functions-aux (stname fta sr sw tr-table w mksym-pkg)
  (declare (xargs :mode :program))
  (b* ((size      (cdr (assoc :size-key fta)))
       (field     (cdr (assoc :field-name fta)))
       (key       (cdr (assoc :field-key fta)))
       (type      (cdr (assoc :type fta)))
       (accessor  (cdr (assoc :accessor-name fta)))
       (updater   (cdr (assoc :updater-name fta)))
       (acc       (mksym '@ field))
       (upd       (mksym '! field))
       (vvar      (mksym 'v))

       ((unless size)
        ;; scalar -- just getter and setter
        (b* ((guard (acl2::translate-declaration-to-guard type vvar w))
             (acc-concl
              (acl2::translate-declaration-to-guard
               type
               `(,sr ,key nil ,stname)
               w)))
          `((defun-inline ,acc (,stname)
              (declare (xargs :guard t
                              :stobjs ,stname))
              (mbe :logic (,sr ,key nil ,stname)
                   :exec  (,accessor ,stname)))
            ,@(if (equal type 'T)
                  `()
                `((defthm ,(mksym sr '- field '-well-formed-value)
                    ,acc-concl)))
            (defun-inline ,upd (,vvar ,stname)
              (declare (xargs :guard ,guard
                              :stobjs ,stname))
              ;; fix is nil for fields of type 'T.
              (mbe :logic (,sw ,key nil ,vvar ,stname)
                   :exec  (,updater ,vvar ,stname))))))

       ;; ((unless (and (eql (len type) 3)
       ;;               (consp (third type))))
       ;;  (er hard? 'mbe-accessor/updater-functions-aux
       ;;      "~% Expected an array declaration for ~p0, but got ~p1 instead."
       ;;      field type))
       ;; (acc-concl
       ;;  (acl2::translate-declaration-to-guard
       ;;   (second type)
       ;;   `(,sr ,key ,ivar ,stname)
       ;;   w))
       (typed-rec (cdr (assoc :typed-record fta)))
       (tr-entry (cdr (assoc typed-rec tr-table)))
       ((unless tr-entry)
        (er hard? 'make-fta
            "Field ~x0 is supposed to be a ~x1 typed record, but this ~
                     doesn't appear to be a typed record: it must have an ~
                     entry in the ~x2 table.  (Typically the name ends in ~
                     -TR-P.)"
            field typed-rec 'typed-records))
       (tr-fi-pairs (cdr (assoc :fi-pairs tr-entry)))
       (elem-p-recog (third (cadr (assoc 'elem-p tr-fi-pairs))))
       (old-var
        ;; Usually 'x, but might as well get it from the lambda.
        (car (second (cadr (assoc 'elem-p tr-fi-pairs)))))
       (ivar      (mksym 'i))
       (acc-concl (subst `(,sr ,key ,ivar ,stname) old-var elem-p-recog))
       (length    (cdr (assoc :length-name fta)))
       (guard     (acl2::translate-declaration-to-guard
                   (second type) vvar w)))

    `((defun-inline ,acc (,ivar ,stname)
        (declare (xargs :stobjs ,stname
                        :guard (and (natp ,ivar)
                                    (< ,ivar (,length ,stname)))))
        (mbe :logic (,sr ,key ,ivar ,stname)
             :exec  (,accessor ,ivar ,stname)))
      (defthm ,(mksym sr '- field '-well-formed-value)
        ,acc-concl)
      (defun-inline ,upd (,ivar ,vvar ,stname)
        (declare (xargs :stobjs ,stname
                        :guard (and (natp ,ivar)
                                    (< ,ivar (,length ,stname))
                                    ,guard)))
        (mbe :logic (,sw ,key ,ivar ,vvar ,stname)
             :exec  (,updater ,ivar ,vvar ,stname))))))

(defun mbe-accessor/updater-functions (stname ftas sr sw tr-table w mksym-pkg)
  (declare (xargs :mode :program))
  (if (atom ftas)
      nil
    (append (mbe-accessor/updater-functions-aux
             stname (car ftas) sr sw tr-table w mksym-pkg)
            (mbe-accessor/updater-functions
             stname (cdr ftas) sr sw tr-table w mksym-pkg))))

(defun make-array-fields-kwd-list (ftas)
  (declare (xargs :mode :program))
  (b* (((when (atom ftas)) nil)
       (fta (car ftas))
       (rest (make-array-fields-kwd-list (cdr ftas)))
       (field-key (cdr (assoc :field-key fta)))
       ((when (cdr (assoc :size-key fta))) ;; array field
        (cons field-key rest)))
    rest))

(defconst *defrstobj-keywords*
  (append acl2::*defstobj-keywords*
          (list :accessor ;; Top-level accessor
                :updater  ;; Top-level updater
                )))

(defun defrstobj-fn (name args wrld)
  (declare (ignorable wrld)
           (xargs :mode :program))
  (b* ((mksym-pkg     name)

       ((mv erp rsfs st-kw-alist)
        (partition-rest-and-keyword-args args *defrstobj-keywords*))
       (- (or (not erp)
              (er hard? 'defrstobj-fn "Invalid DEFRSTOBJ syntax for ~x0." name)))
       (- (or (consp rsfs)
              (er hard? 'defrstobj-fn "Expected at least one field for ~x0." name)))
       ((mv sr sw st-kw-alist)
        ;; sr: state read
        ;; sw: state write
        (let* ((sr-pair (assoc-equal :accessor st-kw-alist))
               (sw-pair (assoc-equal :updater st-kw-alist)))
          (if (and sr-pair sw-pair)
              (mv (cdr sr-pair)
                  (cdr sw-pair)
                  (remove1-assoc-equal
                   :updater
                   (remove1-assoc-equal :accessor st-kw-alist)))
            (mv nil nil st-kw-alist))))

       (tr-alist      (tr-alist rsfs))
       (fix-alist     (fix-alist rsfs))
       (st-fields     (eat-typed-records rsfs))
       (st-kw-part    (alist-to-keyword-alist st-kw-alist nil))
       (name$c        (mksym name '$c))
       (st-fields$c   (make-$c-fields st-fields mksym-pkg))
       (st-template   (defstobj-template name$c (append st-fields$c st-kw-part) wrld))
       ((list recog$c create$c st$c-fld-templates
; Matt K. mod: :doc is no longer supported for defstobj after v7-1
              ;; ?doc
              ?inline ?congruent-to
              ?non-memoizable)
        ;; BOZO this has to be kept in sync with defstobj-template.
        (destructure-defstobj-template st-template))

       (tr-table      (table-alist 'typed-records wrld))

       (ftas (make-ftas tr-alist st$c-fld-templates fix-alist mksym-pkg tr-table))

       (stobj-args    (append st-fields$c st-kw-part))
       (recog         (mksym name 'p))
       (recog$a       (mksym recog '$a))
       (create        (mksym 'create- name))
       (create$a      (mksym create '$a))
       (valfix        (mksym name '- 'valfix))
       (array-fields-kwd-lst (make-array-fields-kwd-list ftas)))

    `(with-output
       :off (event acl2::prove)
       :summary-off (:other-than acl2::form time)
       (encapsulate
         ()

         (logic)
         (set-inhibit-warnings "non-rec" "disable" "subsume") ;; implicitly local


         (local (defthm plus-collect-consts
                  (implies (syntaxp (and (quotep x) (quotep y)))
                           (equal  (+ x y z)
                                   (+ (+ x y) z)))))

         (local
          (progn
            ,@(scalar-fixing-function-thms ftas wrld mksym-pkg)))


         (local (set-default-hints nil))

         (local (in-theory #!acl2
                           (e/d**
                            ((:t nfix)
                             natp-compound-recognizer
                             zp-compound-recognizer
                             nth-of-repeat
                             len-of-repeat
                             append-to-nil
                             (:t repeat)
                             make-list-ac-removal
                             nth-when-atom
                             nth-0-cons
                             nth-add1
                             car-cons cdr-cons
                             nfix-when-natp
                             length
                             len-of-cons
                             len-when-atom
                             update-nth-array
                             nth-update-nth
                             len-update-nth
                             max
                             (:t len)
                             resize-list-when-zp
                             (:rules-of-class :executable-counterpart :here))
                            ((make-list-ac)
                             (repeat)))))

         (local (in-theory (e/d
                            (plus-collect-consts
                             field-map-key-lookup-open
                             field-map-key-lookup-recur-open
                             ,@(scalar-fixing-function-thm-names ftas mksym-pkg)
                             . ,(collect-typed-rec-theorems
                                 ftas (table-alist 'typed-records wrld)))
                            ((field-map-key-lookup-recur)))))


; Get into a very restricted theory that (hopefully) just includes what we need.


         (defstobj ,name$c ,@stobj-args)

         ;; At the moment this is just emptying functions for resizable array
         ;; fields.  Could add others.
         ,@(additional-exec-defs name$c ftas mksym-pkg)

         (defun ,recog$a (x)
           (declare (xargs :guard t)
                    (ignorable x))
           t)

         (defun ,create$a ()
           (declare (xargs :guard t))
           (let* ((x nil)
                  . ,(creator-logic-updates ftas))
             x))

         ,@(logic-field-functions ftas wrld tr-table mksym-pkg)

         (local
          (progn

            (defconst *rstobj-tmp-field-map*
              (list . ,(make-fieldmap-entries ftas)))

            (defund rstobj-tmp-field-map () *rstobj-tmp-field-map*)

            (defun rstobj-tmp-tr-get (name i tr)
              (declare (ignorable name i tr))
              (case name
                . ,(make-tr-get-entries ftas tr-table)))

            (defun rstobj-tmp-tr-set (name i v tr)
              (declare (ignorable name i v tr))
              (case name
                . ,(make-tr-set-entries ftas tr-table)))

            (defun rstobj-tmp-tr-fix (name v)
              (declare (ignorable name v))
              (case name
                . ,(make-tr-fix-entries ftas tr-table)))

            (defun rstobj-tmp-tr-default (name)
              (declare (ignorable name))
              (case name
                . ,(make-tr-default-entries ftas tr-table)))


            (defun rstobj-tmp-tr-elem-p (name v)
              (declare (ignorable name v))
              (case name . ,(make-tr-elem-p-entries ftas tr-table)))

            (defun rstobj-tmp-scalar-fix (name v)
              (declare (ignorable name v))
              (case name
                . ,(make-scalar-fix-entries ftas)))

            (defun rstobj-tmp-scalar-elem-p (name v)
              (declare (ignorable name v))
              (case name
                . ,(make-scalar-elem-p-entries ftas wrld)))

            ;; these type-prescriptions cause trouble when there are
            ;; either no arrays or no scalars
            (in-theory (disable (:t rstobj-tmp-field-map)
                                (:t rstobj-tmp-tr-get)
                                (:t rstobj-tmp-tr-set)
                                (:t rstobj-tmp-tr-fix)
                                (:t rstobj-tmp-tr-default)
                                (:t rstobj-tmp-tr-elem-p)
                                (:t rstobj-tmp-scalar-fix)
                                (:t rstobj-tmp-scalar-elem-p)))

            (defun-sk rstobj-tmp-field-corr (st$c st$a)
              (forall (idx i)
                      (let ((entry (nth idx (rstobj-tmp-field-map))))
                        (and (implies (equal (acl2::tag entry) :array)
                                      ;; array
                                      (b* (((array-fieldinfo x) entry)
                                           (arr (nth idx st$c))
                                           (tr  (g x.tr-key st$a)))
                                        (and (implies (natp i)
                                                      (equal (rstobj-tmp-tr-get x.tr-key i tr)
                                                             (if (< i (len arr))
                                                                 (nth i arr)
                                                               (rstobj-tmp-tr-default x.tr-key))))
                                             (equal (g x.size-key st$a)
                                                    (len arr)))))
                             (implies (equal (acl2::tag entry) :scalar)
                                      (b* (((scalar-fieldinfo x) entry))
                                        (equal (g x.key st$a)
                                               (nth idx st$c)))))))
              :rewrite :direct)

            (in-theory (disable rstobj-tmp-field-corr rstobj-tmp-field-corr-necc))


            (defthm rstobj-tmp-field-corr-of-size-key
              (mv-let (keytype idx)
                (field-map-key-lookup szkey (rstobj-tmp-field-map))
                (implies (and (rstobj-tmp-field-corr st$c st$a)
                              (equal keytype :size))
                         (equal (g szkey st$a)
                                (len (nth idx st$c)))))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-size-key
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :in-theory (disable (rstobj-tmp-field-map)
                                           rstobj-tmp-tr-get
                                           rstobj-tmp-tr-fix
                                           rstobj-tmp-scalar-fix
                                           rstobj-tmp-scalar-elem-p
                                           rstobj-tmp-tr-default
                                           rstobj-tmp-tr-set)
                       :do-not-induct t)
                      (let ((lit (car clause)))
                        (case-match lit
                          ((f ('rstobj-tmp-field-corr . &) . &)
                           `(:in-theory (e/d ,(if (eq f 'equal)
                                                  '(rstobj-tmp-field-corr)
                                                '(rstobj-tmp-field-corr-necc))
                                             ((rstobj-tmp-field-map)
                                              rstobj-tmp-tr-get
                                              rstobj-tmp-tr-fix
                                              rstobj-tmp-scalar-fix))))
                          (('if . &) nil)
                          (('implies . &) nil)
                          (& '(:in-theory (enable)))))))

            (defthm rstobj-tmp-field-corr-of-scalar-key
              (mv-let (keytype idx)
                (field-map-key-lookup sckey (rstobj-tmp-field-map))
                (implies (and (rstobj-tmp-field-corr st$c st$a)
                              (equal keytype :scalar))
                         (equal (g sckey st$a)
                                (nth idx st$c))))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-scalar-key
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :do-not-induct t)))

            (defthm rstobj-tmp-field-corr-of-tr-key
              (mv-let (keytype idx)
                (field-map-key-lookup trkey (rstobj-tmp-field-map))
                (implies (and (rstobj-tmp-field-corr st$c st$a)
                              (equal keytype :array)
                              (natp i))
                         (equal (rstobj-tmp-tr-get trkey i (g trkey st$a))
                                (if (< i (len (nth idx st$c)))
                                    (nth i (nth idx st$c))
                                  (rstobj-tmp-tr-default trkey)))))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-tr-key
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :do-not-induct t)))

            ,@(let ((concls (make-field-corr-of-tr-key-concls ftas tr-table)))
                (and concls
                     `((defthm rstobj-tmp-field-corr-of-tr-key-elaborate
                         (mv-let (keytype idx)
                           (field-map-key-lookup trkey (rstobj-tmp-field-map))
                           (implies (and (rstobj-tmp-field-corr st$c st$a)
                                         (equal keytype :array)
                                         (natp i))
                                    (and . ,concls)))
                         :hints (("goal" :use rstobj-tmp-field-corr-of-tr-key
                                  :in-theory (e/d (rstobj-tmp-tr-get) (rstobj-tmp-field-corr-of-tr-key))))))))


            (defthm rstobj-tmp-field-corr-of-update-scalar
              (implies (and (rstobj-tmp-field-corr st$c st$a)
                            (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :scalar)
                            (equal (scalar-fieldinfo->key (nth idx (rstobj-tmp-field-map))) key)
                            (equal v (rstobj-tmp-scalar-fix key v)))
                       (rstobj-tmp-field-corr (update-nth idx v st$c)
                                              (s key v st$a)))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-update-scalar
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :do-not-induct t)))




            (defthm rstobj-tmp-field-corr-of-update-array
              (implies (and (rstobj-tmp-field-corr st$c st$a)
                            (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :array)
                            (equal (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))) key)
                            (equal tr1 (rstobj-tmp-tr-set key i v (g key st$a)))
                            (equal v (rstobj-tmp-tr-fix key v))
                            (natp i)
                            (< i (len (nth idx st$c))))
                       (rstobj-tmp-field-corr (update-nth idx (update-nth i v (nth idx st$c))
                                                          st$c)
                                              (s key tr1 st$a)))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-update-array
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :do-not-induct t)))


            (defthm rstobj-tmp-field-corr-of-grow-array
              (implies (and (rstobj-tmp-field-corr st$c st$a)
                            (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :array)
                            (equal (array-fieldinfo->size-key (nth idx (rstobj-tmp-field-map))) size-key)
                            (natp new-size)
                            (<= (len (nth idx st$c)) new-size)
                            (equal default (rstobj-tmp-tr-default
                                            (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))))))
                       (rstobj-tmp-field-corr (update-nth idx
                                                          (resize-list (nth idx st$c) new-size default)
                                                          st$c)
                                              (s size-key new-size st$a)))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-grow-array
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :do-not-induct t)))

            (defthm rstobj-tmp-field-corr-of-empty-array
              (implies (and (rstobj-tmp-field-corr st$c st$a)
                            (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :array)
                            (equal (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))) tr-key)
                            (equal (array-fieldinfo->size-key (nth idx (rstobj-tmp-field-map))) size-key))
                       (rstobj-tmp-field-corr (update-nth idx nil st$c)
                                              (s tr-key nil (s size-key 0 st$a))))
              :hints (("goal" :by (:instance
                                   (:functional-instance
                                    rstobj-field-corr-of-empty-array
                                    (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                    (rstobj-field-corr rstobj-tmp-field-corr)
                                    (rstobj-field-map rstobj-tmp-field-map)
                                    (rstobj-tr-get rstobj-tmp-tr-get)
                                    (rstobj-tr-set rstobj-tmp-tr-set)
                                    (rstobj-tr-fix rstobj-tmp-tr-fix)
                                    (rstobj-tr-default rstobj-tmp-tr-default)
                                    (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                    (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                    (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                   (rstobj$c st$c)
                                   (rstobj$a st$a))
                       :do-not-induct t)))


            (defthm rstobj-tmp-field-corr-of-create
              (rstobj-tmp-field-corr (,create$c) (,create$a))
              :hints(("Goal" :in-theory (e/d (rstobj-tmp-field-corr))
                      :expand ((:free (a b c) (nth a (cons b c)))))))


            (defun-nx rstobj-tmp-corr (,name$c x)
              (and (,recog$c ,name$c)
                   (rstobj-tmp-field-corr ,name$c x)))

            (defthm field-lookup-in-rstobj-tmp-field-map
              (implies (syntaxp (quotep key))
                       (equal (field-map-key-lookup key (rstobj-tmp-field-map))
                              (field-map-key-lookup key *rstobj-tmp-field-map*))))

            (defthm index-lookup-in-rstobj-tmp-field-map
              (implies (syntaxp (quotep idx))
                       (equal (nth idx (rstobj-tmp-field-map))
                              (nth idx *rstobj-tmp-field-map*))))


            ,@(array-types-preserved-thms ftas wrld mksym-pkg)

            (set-default-hints
             '((and stable-under-simplificationp
                    '(:in-theory (enable ,create$a ,create$c ,recog$c)))))))

         (local (in-theory (disable
                            (rstobj-tmp-field-corr)
                            (rstobj-tmp-field-map)
                            ,recog$c
                            ,create$a
                            (,create$a)
                            ,create$c
                            (,create$c))))

         (acl2::defabsstobj-events ,name
           :concrete ,name$c
           :corr-fn rstobj-tmp-corr
           :creator (,create :logic ,create$a :exec ,create$c)
           :recognizer (,recog :logic ,recog$a :exec ,recog$c)
           :exports
           ,(absstobj-exports ftas mksym-pkg))

         ;; For the accessor/updater functions:

         ,@(and sr sw
                (b* ((fld (mksym 'fld))
                     (fld1 (mksym 'fld1))
                     (fld2 (mksym 'fld2))
                     (index (mksym 'index))
                     (value (mksym 'value))
                     (i (mksym 'i))
                     (j (mksym 'j))
                     (v (mksym 'v))
                     (x (mksym 'x))
                     (i1 (mksym 'i1))
                     (v1 (mksym 'v1))
                     (i2 (mksym 'i2))
                     (v2 (mksym 'v2))
                     (st (mksym 'st)))

                  `((progn

                      (defun ,(mksym name '- 'valfix) (,fld ,x)
                        (case ,fld
                          ,@(make-val-fixing-fn ftas tr-table)))

                      (defun-nx ,sr (,fld ,index ,name)
                        (declare (xargs
                                  :stobjs ,name
                                  :guard (case ,fld
                                           ,@(guards-for-top-level-acc/upd
                                              name :getter ftas mksym-pkg wrld))))
                        (case ,fld
                          ,@(top-level-getter-fns name ftas mksym-pkg)))

                      (defun-nx ,sw (,fld ,index ,value ,name)
                        (declare (xargs :stobjs ,name
                                        :guard (case ,fld
                                                 ,@(guards-for-top-level-acc/upd
                                                    name :setter ftas mksym-pkg wrld))))
                        (case ,fld
                          ,@(top-level-setter-fns name ftas mksym-pkg)))

                      ;; Preservation Theorem
                      (defthm ,(mksym recog '-of- sw)
                        (,recog (,sw ,fld ,index ,value ,st)))

                      (local (in-theory (e/d (acl2::g-same-s
                                              acl2::g-diff-s
                                              acl2::g-of-s-redux
                                              acl2::s-same-g
                                              acl2::s-same-s
                                              acl2::s-diff-s)
                                             ())))

                      ;; RoW Theorems
                      (defthm ,(mksym sr '- sw '-intra-field)
                        (equal (,sr ,fld ,i (,sw ,fld ,j ,v ,st))
                               (if (member ,fld ',array-fields-kwd-lst)
                                   (if (equal ,i ,j)
                                       (,valfix ,fld ,v)
                                     (,sr ,fld ,i ,st))
                                 (,valfix ,fld ,v)))
                        :hints (("Goal" :in-theory (e/d (member) ()))))

                      (defthm ,(mksym sr '- sw '-inter-field)
                        (implies (case-split (not (equal ,fld1 ,fld2)))
                                 (equal (,sr ,fld2 ,i2 (,sw ,fld1 ,i1 ,v ,st))
                                        (,sr ,fld2 ,i2 ,st))))

                      ;; WoW Theorems:
                      (defthm ,(mksym sw '- sw '-shadow-writes)
                        (equal (,sw ,fld ,i ,v2 (,sw ,fld ,i ,v1 ,st))
                               (,sw ,fld ,i ,v2 ,st))
                        :hints (("Goal" :in-theory (e/d (member) ()))))

                      (defthm ,(mksym sw '- sw '-intra-field-arrange-writes)
                        (implies (and (member ,fld ',array-fields-kwd-lst)
                                      (not (equal ,i1 ,i2)))
                                 (equal (,sw ,fld ,i2 ,v2 (,sw ,fld ,i1 ,v1 ,st))
                                        (,sw ,fld ,i1 ,v1 (,sw ,fld ,i2 ,v2 ,st))))
                        :hints (("Goal" :in-theory (e/d (member) ())))
                        :rule-classes ((:rewrite :loop-stopper ((,i2 ,i1)))))

                      (defthm ,(mksym sw '- sw '-inter-field-arrange-writes)
                        (implies (not (equal ,fld1 ,fld2))
                                 (equal (,sw ,fld2 ,i2 ,v2 (,sw ,fld1 ,i1 ,v1 ,st))
                                        (,sw ,fld1 ,i1 ,v1 (,sw ,fld2 ,i2 ,v2 ,st))))
                        :rule-classes ((:rewrite :loop-stopper ((,fld2 ,fld1)))))

                      ;; From now on, use functions SR and SW for reasoning instead of
                      ;; get-* and set-*.

                      ,@(mbe-accessor/updater-functions
                         name ftas sr sw tr-table wrld mksym-pkg)

                      (in-theory (e/d () (,sr ,sw)))))))))))

(defmacro defrstobj (name &rest args)
  `(make-event
    (defrstobj-fn ',name ',args (w state))))

(logic)
(local
 (progn

   ;; Very basic test: more tests in basic-tests.lisp

   (defun ubp-listp (n x)
     (declare (xargs :guard t))
     (if (atom x)
         (not x)
       (and (unsigned-byte-p n (car x))
            (ubp-listp n (cdr x)))))

   (defun ubp-fix (n x)
     (declare (xargs :guard t))
     (if (unsigned-byte-p n x)
         x
       0))

   (def-typed-record ubp8
     :elem-p       (unsigned-byte-p 8 x)
     :elem-list-p  (ubp-listp 8 x)
     :elem-default 0
     :elem-fix     (ubp-fix 8 x))


   (defun nonneg-fix (x)
     (declare (xargs :guard t))
     (if (integerp x)
         (if (< x 0)
             (- x)
           x)
       0))

   (def-typed-record nonneg
     :elem-p (natp x)
     :elem-list-p (nat-listp x)
     :elem-default 0
     :elem-fix (nonneg-fix x))

   (defrstobj st

     (natarr  :type (array (integer 0 *) (32))
              :initially 0
              :typed-record nonneg-tr-p)

     (u8arr   :type (array (unsigned-byte 8) (64))
              :initially 0
              :typed-record ubp8-tr-p
              :resizable t)

     (intfld  :type integer
              :initially 5
              :fix (ifix x))

     (natfld :type (integer 0 *)
             :initially 0
             :fix (nonneg-fix x))

     :accessor read-st
     :updater  write-st)))
