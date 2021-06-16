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
; Author: Sol Swords <sswords@centtech.com>
; Based on previous work by Jared Davis and Shilpi Goel <shilpi@centtech.com>
;   -- see ../defrstobj/defrstobj.lisp.
; Shilpi Goel <shilpi@centtech.com>: added support for child stobjs (04/09/2021)

(in-package "RSTOBJ2")
(include-book "def-multityped-record")
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
  :long " <p>Defrstobj creates an abstract stobj where the concrete stobj
contains some user-specified scalar fields, fixed-length array fields, and child stobjs, but
the logical interface is that of a multityped record (see @(see
def-multityped-record)).  The executable accessors/updaters expand to calls of
a single multityped record accessor/updater so that only a small number of
theorems are needed for reasoning about reads over writes, and writes over
writes, etc.</p>

<p>This topic pertains only to @('rstobj2::defrstobj'), defined in
@('centaur/defrstobj2/defrstobj.lisp').  A previous version,
@('rstobj::defrstobj'), is defined in @('centaur/defrstobj/defrstobj.lisp'),
and another one before that in @('projects/legacy-defrstobj/defrstobj.lisp').</p>

<p>The main difference between this version and previous versions is the logical
interface.  In previous versions the top-level stobj was an untyped record
containing certain keys (those corresponding to array fields) that were
uniformly typed records.  In this version, the entire stobj is a multityped
record and the array contents are not their own subfields.</p>

<h4>Invocation and Options</h4>
<p>Example invocations:</p>
@({
 (defrstobj myst
   (u32-scalar :type (unsigned-byte 32) :initially 0 :fix (ec-call (acl2::loghead$inline 32 x)))
   (u32-array :type (array (unsigned-byte 32) (16)) :initially 5 :fix (acl2::loghead 32 (ifix x)))
   (nat-scalar :type (integer 0 *) :initially 6 :fix (nfix x))
   (nat-array :type (array (integer 0 *) (12)) :initially 8 :fix (nfix x)))
 
 (defrstobj parent
   (parent-nat-scalar :type (integer 0 *) :initially 0 :fix (nfix x))
   ;; \"Exporting\" two fields from the child stobj into this parent stobj
   (child-u32-array :type (array (unsigned-byte 32) (16))
                    :initially 5
                    :fix (acl2::loghead 32 (ifix x))
                    :child-stobj child
                    :child-accessor get-u32-array
                    :child-updater  set-u32-array)
   (child-u32-scalar :type (unsigned-byte 32)
                     :initially 0
                     :fix (acl2::loghead 32 (ifix x))
                     :child-stobj child
                     :child-accessor get-u32-scalar
                     :child-updater  set-u32-scalar)
   :enable '(get-u32-array-over-set-u32-array
             get-u32-scalar-over-set-u32-scalar
             get-u32-array-default-value
             get-u32-scalar-default-value))

 })

<p>The first argument to @('defrstobj') is the name of the abstract stobj
to generate; the rest of the arguments are field specifiers and top-level
keyword options, as follows:</p>

<ul>
<li>@(':recname') -- name of the multityped record to generate, default @('<name>rec')</li>
<li>@(':inline') -- inline the concrete stobj accessor/updaters; default T</li>
<li>@(':non-memoizable') -- declare the concrete stobj non-memoizable; default NIL</li>
<li>@(':concrete-stobj') -- name of the concrete stobj, default @('<name>$c')</li>
<li>@(':pkg-sym') -- symbol in whose package all new names will be generated, default @('name')</li>
<li>@(':elem-p') -- name of the element predicate function to be generated, default @('<name>-elem-p')</li>
<li>@(':elem-fix') -- name of the element fixing function to be generated, default @('<name>-elem-fix')</li>
<li>@(':elem-default') -- name of the element default function to be generated, default @('<name>-elem-default')</li>
<li>@(':logic-stobj') -- variable name to use for the logical analogue of the
stobj in the logic definitions of the accessors and updaters; default
@('<name>$a')</li>
<li>@(':recognizer') -- name of the stobj recognizer function; default @('<name>p')</li>
<li>@(':logic-recognizer') -- logic version of the stobj recognizer function; default @('<logic-stobj>p')</li>
<li>@(':creator') -- name of the stobj creator function; default @('create-<name>')</li>
<li>@(':logic-creator') -- logic version of the stobj creator function; default @('create-<logic-stobj>')</li>
<li>@(':accessor-template') -- list of symbols whose names will be concatenated
to generate the name of a field accessor, where @('acl2::x') stands for the name of
a field; default @('(get- x)')</li>
<li>@(':updater-template') -- list of symbols whose names will be concatenated
to generate the name of a field updater, where @('acl2::x') stands for the name
of a field; default @('(set- x)')</li>
<li>@(':accessor') -- name of the generic accessor; default is generated from
the accessor template by substituting @('name') for @('x'); therefore the
default for the default accessor template is @('get-<name>')</li>
<li>@(':updater') -- name of the generic updater; default is generated from the
updater template by substituting @('name') for @('x'); therefore the default
for the default updater template is @('set-<name>'). </li>
</ul>

<p>Fields consist of a name followed by a keyword/value list where the
acceptable keys are the following:</p>

<ul>
<li>@(':type') -- the stobj field type, such as @('string') or
@('(array (integer 0 *) (12))'), defaulting to @('t').</li>

<li>@(':pred') -- the element recognizer predicate, as an expression in terms
of @('x'), where the default is generated from @(':type') by applying
@('translate-declaration-to-guard').  May be more specific than the stobj field
type.</li>

<li>@(':fix') -- the element fixing function, as an expression in terms of
@('x'), defaulting to the identity @('x'), which is only valid for untyped
fields</li>

<li>@(':initially') -- the initial value of the field or of an element for
array fields; default @('nil')</li>

<li>@(':accessor') -- the name of the accessor for the field; default is
determined by the @(':accessor-template') top-level argument</li>

<li>@(':updater') -- the name of the updater for the field; default is
determined by the @(':updater-template') top-level argument</li>

<li>@(':logic-accessor') -- the logical version of the accessor function,
default @('<accessor>$a')</li>

<li>@(':logic-updater') -- the logical version of the updater function,
default @('<updater>$a')</li>

<li>@(':child-stobj') -- the name of a previously-introduced stobj</li>

<li>@(':child-accessor') -- the name of an accessor function of some
field of the child stobj</li>

<li>@(':child-updater') -- the name of an updater function of some
field of the child stobj</li>

<li>@(':key') -- the keyword corresponding to the field, for use as a key in
the typed record.</li>
</ul>

<p>When a field is based off a child stobj, then @('defrstobj')
requires certain theorems about the child stobj's accessors and
updaters to be made available to it using the top-level keyword option
@(':enable').  Two kinds of theorems are expected:</p>

<ul>

<li>Non-interference Theorems -- standard accessor/updater
independence or read-over-write theorems. Also see @(see
stobjs::stobj-updater-independence) and @('std/stobjs/nicestobj') for
a possible strategy to adopt to prove these kinds of theorems.</li>

<li>Default-value Theorems -- theorems stating that calling the
accessor on a stobj's creator function returns the default value.</li>

</ul>")


(logic)

(defund all-equal (x)
  (if (or (atom x)
          (atom (cdr x)))
      t
    (and (equal (car x) (cadr x))
         (all-equal (cdr x)))))

(defthmd nth-when-all-equal
  (implies (And (all-equal x)
                (natp n)
                (< n (len x)))
           (equal (nth n x) (car x)))
  :hints(("Goal" :in-theory (enable all-equal))))

(defthmd nth-of-cons  
  ;; Deals with the following kinds of terms that appear during the
  ;; proof of create-st{correspondence} when a child stobj's creator
  ;; function shows up somewhere in the second arg. of nth and
  ;; nth-when-all-equal doesn't work.
  ;; (EQUAL 0 (NTH 1 (CONS (CREATE-CHILD) '(0))))
  ;; (EQUAL 0 (NTH 0 (LIST 0 (CREATE-CHILD))))
  ;; (EQUAL 0 (NTH 0 (LIST* 0 (CREATE-CHILD) '(0))))
  (implies (syntaxp (or (not (quotep x))
                        (not (quotep y))))
           (equal (nth n (cons x y))
                  (if (zp n)
                      x
                    (nth (1- n) y)))))






;; Example

#||

(defrstobj myst
  (u32-scalar :type (unsigned-byte 32) :initially 0 :fix (acl2::loghead 32 (ifix x)))
  (u32-array :type (array (unsigned-byte 32) (16)) :initially 5 :fix (acl2::loghead 32 (ifix x)))
  (nat-scalar :type (integer 0 *) :initially 6 :fix (nfix x))
  (nat-array :type (array (integer 0 *) (12)) :initially 8 :fix (nfix x)))


(local (include-book "centaur/bitops/ihsext-basics" :Dir :System))

(defstobj myst$c
  (myst$c-u32-scalar :type (unsigned-byte 32) :initially 0)
  (myst$c-u32-array :type (array (unsigned-byte 32) (16)) :initially 5)
  ;; (myst$c-u32-fix-scalar :type (unsigned-byte 32) :initially 10)
  ;; (myst$c-u32-fix-array :type (array (unsigned-byte 32) (24)) :initially 0)
  (myst$c-nat-scalar :type (integer 0 *) :initially 6)
  (myst$c-nat-array :type (array (integer 0 *) (12)) :initially 8))

(defun myst-elem-p (key x)
  (declare (xargs :guard t))
  (if (consp key)
      (case (car key)
        (:u32-scalar (unsigned-byte-p 32 x))
        (:u32-array (unsigned-byte-p 32 x))
        ;; (:u32-fix-scalar (natp x))
        ;; (:u32-fix-array (natp x))
        (:nat-scalar (natp x))
        (:nat-array (natp x))
        (otherwise t))
    t))

(local (defthm myst-elem-p-of-cons
         (implies (syntaxp (quotep k))
                  (equal (myst-elem-p (cons k idx) x)
                         (case k
                           (:u32-scalar (unsigned-byte-p 32 x))
                           (:u32-array (unsigned-byte-p 32 x))
                           ;; (:u32-fix-scalar (natp x))
                           ;; (:u32-fix-array (natp x))
                           (:nat-scalar (natp x))
                           (:nat-array (natp x))
                           (otherwise t))))))

(defun myst-elem-fix (key x)
  (declare (xargs :guard t))
  (if (consp key)
      (case (car key)
        (:u32-scalar (acl2::loghead 32 (ifix x)))
        (:u32-array (acl2::loghead 32 (ifix x)))
        ;; (:u32-fix-scalar (nfix x))
        ;; (:u32-fix-array (nfix x))
        (:nat-scalar (nfix x))
        (:nat-array (nfix x))
        (otherwise x))
    x))

(local (defthm myst-elem-fix-of-cons
         (implies (syntaxp (quotep k))
                  (equal (myst-elem-fix (cons k idx) x)
                         (case k
                           (:u32-scalar (acl2::loghead 32 (ifix x)))
                           (:u32-array (acl2::loghead 32 (ifix x)))
                           ;; (:u32-fix-scalar (nfix x))
                           ;; (:u32-fix-array (nfix x))
                           (:nat-scalar (nfix x))
                           (:nat-array (nfix x))
                           (otherwise x))))))

(defun myst-elem-default (key)
  (declare (xargs :guard t))
  (if (consp key)
      (case (car key)
        (:u32-scalar 0)
        (:u32-array 5)
        ;; (:u32-fix-scalar 10)
        ;; (:u32-fix-array 0)
        (:nat-scalar 6)
        (:nat-array 8)
        (otherwise nil))
    nil))

(local (defthm myst-elem-default-of-cons
         (implies (syntaxp (quotep k))
                  (equal (myst-elem-default (cons k idx))
                         (case k
                           (:u32-scalar 0)
                           (:u32-array 5)
                           ;; (:u32-fix-scalar 10)
                           ;; (:u32-fix-array 0)
                           (:nat-scalar 6)
                           (:nat-array 8)
                           (otherwise nil))))))

(def-multityped-record mystrec
  :elem-p (myst-elem-p k x)
  :elem-fix (myst-elem-fix k x)
  :elem-default (myst-elem-default k))

(local (in-theory (disable myst-elem-p
                           myst-elem-fix
                           myst-elem-default)))

(defun myst$a-p (myst$a)
  (declare (xargs :guard t))
  ;; (and (mystrec-p myst$a)
  (not (mystrec-bad-part myst$a)))

(defun myst$a-u32-scalar (myst$a)
  (declare (xargs :guard t))
  (mystrec-get '(:u32-scalar) myst$a))

(defun update-myst$a-u32-scalar (v myst$a)
  (declare (xargs :guard (unsigned-byte-p 32 v)))
  (mystrec-set '(:u32-scalar) v myst$a))

(defun myst$a-u32-arrayi (idx myst$a)
  (declare (xargs :guard (and (natp idx)
                              (< idx 16))))
  (mystrec-get (cons :u32-array (nfix idx)) myst$a))

(defun update-myst$a-u32-arrayi (idx v myst$a)
  (declare (xargs :guard (and (natp idx)
                              (< idx 16)
                              (unsigned-byte-p 32 v))))
  (mystrec-set (cons :u32-array (nfix idx)) v myst$a))

(defun myst$a-nat-scalar (myst$a)
  (declare (xargs :guard t))
  (mystrec-get '(:nat-scalar) myst$a))

(defun update-myst$a-nat-scalar (v myst$a)
  (declare (xargs :guard (unsigned-byte-p 32 v)))
  (mystrec-set '(:nat-scalar) v myst$a))

(defun myst$a-nat-arrayi (idx myst$a)
  (declare (xargs :guard (and (natp idx)
                              (< idx 12))))
  (mystrec-get (cons :nat-array (nfix idx)) myst$a))

(defun update-myst$a-nat-arrayi (idx v myst$a)
  (declare (xargs :guard (and (natp idx)
                              (< idx 12)
                              (unsigned-byte-p 32 v))))
  (mystrec-set (cons :nat-array (nfix idx)) v myst$a))

;; (defun myst$a-u32-array-delete-range (max min myst$a)
;;   (declare (xargs :measure (nfix (- (nfix max) (nfix min)))))
;;   (if (zp (- (nfix max) (nfix min)))
;;       myst$a)
;;   (myst$a-u32-array-delete-range
;;    (- (nfix max) 1) min (mystrec-set (cons :nat-array (- (nfix max) 1)) myst$a)))

(defun create-myst$a ()
  (declare (xargs :guard t))
  nil)






(encapsulate nil
  (local
   (progn
     (in-theory (disable nth update-nth
                         acl2::nth-when-zp
                         nth-add1))

     (defun-sk myst-u32-array-corr (myst$c myst$a)
       (forall idx
               (implies (< (nfix idx) 16)
                        (equal (nth idx (nth *myst$c-u32-arrayi* myst$c))
                               (mystrec-get (cons :u32-array (nfix idx)) myst$A))))
       :rewrite :direct)
     (in-theory (disable myst-u32-array-corr))

     (defthm myst-u32-array-corr-of-update-other
       (implies (and (myst-u32-array-corr myst$c myst$a)
                     (not (equal (nfix field-index) *myst$c-u32-arrayi*))
                     (not (equal field-key :u32-array)))
                (myst-u32-array-corr
                 (update-nth field-index new-field myst$c)
                 (mystrec-set (cons field-key idx) val myst$a)))
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause)))))))

     (defthm myst-u32-array-corr-of-update
       (implies (and (myst-u32-array-corr myst$c myst$a)
                     (unsigned-byte-p 32 val)
                     (natp idx))
                (myst-u32-array-corr
                 (update-nth *myst$c-u32-arrayi*
                             (update-nth idx val (nth *myst$c-u32-arrayi* myst$c))
                             myst$c)
                 (mystrec-set (cons :u32-array idx) val myst$a)))
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause)))))))

     (defun-sk myst-nat-array-corr (myst$c myst$a)
       (forall idx
               (implies (< (nfix idx) 12)
                        (equal (nth idx (nth *myst$c-nat-arrayi* myst$c))
                               (mystrec-get (cons :nat-array (nfix idx)) myst$A))))
       :rewrite :direct)

     (in-theory (disable myst-nat-array-corr))

     (defthm myst-nat-array-corr-of-update-other
       (implies (and (myst-nat-array-corr myst$c myst$a)
                     (not (equal (nfix field-index) *myst$c-nat-arrayi*))
                     (not (equal field-key :nat-array)))
                (myst-nat-array-corr
                 (update-nth field-index new-field myst$c)
                 (mystrec-set (cons field-key idx) val myst$a)))
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause)))))))


     (defthm myst-nat-array-corr-of-update
       (implies (and (myst-nat-array-corr myst$c myst$a)
                     (natp val)
                     (natp idx))
                (myst-nat-array-corr
                 (update-nth *myst$c-nat-arrayi*
                             (update-nth idx val (nth *myst$c-nat-arrayi* myst$c))
                             myst$c)
                 (mystrec-set (cons :nat-array idx) val myst$a)))
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause)))))))

     (defun-nx myst-corr (myst$c myst$a)
       (and (equal (myst$a-nat-scalar myst$a)
                   (myst$c-nat-scalar myst$c))
            (equal (myst$a-u32-scalar myst$a)
                   (myst$c-u32-scalar myst$c))
            (myst-nat-array-corr myst$c myst$a)
            (myst-u32-array-corr myst$c myst$a)))
     (in-theory (disable (myst-corr)))

     (set-default-hints
      '((and stable-under-simplificationp
             (let ((lit (car (last clause))))
               (and (consp lit)
                    (member-eq (car lit) '(myst-nat-array-corr myst-u32-array-corr))
                    (prog2$ (cw "Expanding ~x0~%" lit)
                            `(:expand (,lit))))))))

     ;; (defun all-equal (x)
     ;;   (if (or (atom x)
     ;;           (atom (cdr x)))
     ;;       t
     ;;     (and (equal (car x) (cadr x))
     ;;          (all-equal (cdr x)))))

     ;; (defthm nth-when-all-equal
     ;;   (implies (And (< (nfix n) (len x))
     ;;                 (all-equal x))
     ;;            (equal (nth n x) (car x))))

     (in-theory (enable nth-when-all-equal))

     ))

  (acl2::defabsstobj-events myst
    :foundation myst$c
    :corr-fn myst-corr
    :recognizer (mystp :logic myst$a-p :exec myst$cp)
    :creator (create-myst :logic create-myst$a :exec create-myst$c)
    :exports ((myst-u32-scalar :logic myst$a-u32-scalar :exec myst$c-u32-scalar)
              (update-myst-u32-scalar :logic update-myst$a-u32-scalar :exec update-myst$c-u32-scalar)
              (myst-u32-arrayi :logic myst$a-u32-arrayi :exec myst$c-u32-arrayi)
              (update-myst-u32-arrayi :logic update-myst$a-u32-arrayi :exec update-myst$c-u32-arrayi)
              (myst-nat-scalar :logic myst$a-nat-scalar :exec myst$c-nat-scalar)
              (update-myst-nat-scalar :logic update-myst$a-nat-scalar :exec update-myst$c-nat-scalar)
              (myst-nat-arrayi :logic myst$a-nat-arrayi :exec myst$c-nat-arrayi)
              (update-myst-nat-arrayi :logic update-myst$a-nat-arrayi :exec update-myst$c-nat-arrayi))))


||#




(program)

(defmacro mksym-list (lst)
  `(intern-in-package-of-symbol
    (string-append-lst
     (symbol-list-names ,lst))
    mksym-pkg))

;; bozo duplicate with std/stobjs/nicestobj.lisp
(defun kwd-alist-field-accessor-alist (keys)
  (if (atom keys)
      nil
    (cons (cons (car keys)
                `(lambda (x) (cdr (assoc-eq ,(car keys) x))))
          (kwd-alist-field-accessor-alist (cdr keys)))))





(defconst *defrstobj-keys*
  '(:name :recname :inline :non-memoizable :pkg-sym :fields
    :elem-p :elem-fix :elem-default
    :concrete-stobj :logic-stobj
    :recognizer :logic-recognizer
    :creator :logic-creator
    :accessor :updater
    :accessor-template :updater-template
    :enable))

(make-event
 (std::da-make-binder-gen
  'rstobj
  (kwd-alist-field-accessor-alist *defrstobj-keys*)))

(defun parse-defrstobj-field (field x)
  (b* (((unless (and (symbolp (car field))
                     (keyword-value-listp (cdr field))))
        (er hard? 'parse-defrstobj-field "A defrstobj field must be a symbol followed by a keyword-value list, unlike ~x0" x))
       (fieldname (car field))
       (keyvals (cdr field))
       ((rstobj x))
       (mksym-pkg x.pkg-sym)
       (type-look (assoc-keyword :type keyvals))
       (child-stobj-look (assoc-keyword :child-stobj keyvals))
       (child-stobj (if child-stobj-look (cadr child-stobj-look) nil))
       (field-type (if type-look
                     (cadr type-look)
                   t))
       (stobj-type (or child-stobj field-type))
       (arrayp (and (consp field-type)
                    (eq (car field-type) 'array)))
       (hashp (and (consp field-type)
                   (eq (car field-type) 'hash-table)))
       (- (and hashp
               (er hard? 'parse-defrstobj-field
                   "Hash table fields aren't supported yet")))
       (stobj-elt-type (if arrayp
                           (cadr field-type)
                         field-type))
       (pred-look (assoc-keyword :pred keyvals))
       (pred (if pred-look
                 (cadr pred-look)
               (translate-declaration-to-guard stobj-elt-type 'x nil)))
       (fix-look (assoc-keyword :fix keyvals))
       (fix (if fix-look
                (cadr fix-look)
              'x))
       (initially-look (assoc-keyword :initially keyvals))
       (initially (cadr initially-look))
       (resizable-look (assoc-keyword :resizable keyvals))
       (- (and (cadr resizable-look)
               (er hard? 'parse-defrstobj-field
                   "Resizable arrays aren't supported yet")))
       (length (and arrayp (car (caddr field-type))))
       (exec-fieldname (mksym fieldname '$c))
       (child-accessor-look (assoc-keyword :child-accessor keyvals))
       (child-accessor (and child-accessor-look (cadr child-accessor-look)))
       (child-updater-look (assoc-keyword :child-updater keyvals))
       (child-updater (and child-updater-look (cadr child-updater-look)))
       (- (and (xor child-stobj (and child-accessor child-updater))
               (er hard? 'parse-defrstobj-field
                   "Expected either all or none of the following: :child-stobj, :child-accessor, :child-updater")))
       (exec-accessor (if (and arrayp (not child-stobj))
                          (acl2::defstobj-fnname exec-fieldname :accessor :array nil)
                        (acl2::defstobj-fnname exec-fieldname :accessor :scalar nil)))
       (child-exec-accessor (and child-accessor (mksym child-accessor '$c)))
       (child-exec-updater (and child-updater (mksym child-updater '$c)))
       (exec-updater (if (and arrayp (not child-stobj))
                         (acl2::defstobj-fnname exec-fieldname :updater :array nil)
                       (acl2::defstobj-fnname exec-fieldname :updater :scalar nil)))
       (accessor-look (assoc-keyword :accessor keyvals))
       (accessor (if accessor-look
                     (cadr accessor-look)
                   (mksym-list (subst fieldname 'x x.accessor-template))))
       (logic-accessor (mksym accessor '$a))
       (updater-look (assoc-keyword :updater keyvals))
       (updater (if updater-look
                    (cadr updater-look)
                  (mksym-list (subst fieldname 'x x.updater-template))))
       (logic-updater (mksym updater '$a))
       (field-key-look (assoc-keyword :key keyvals))
       (field-key (if field-key-look
                      (cadr field-key-look)
                    (intern-in-package-of-symbol (symbol-name fieldname) :keyword))))
    `((:fieldname . ,fieldname)
      (:field-type . ,field-type)
      (:stobj-type . ,stobj-type)
      (:arrayp . ,arrayp)
      (:pred . ,pred)
      (:fix . ,fix)
      (:initially . ,initially)
      (:child-stobj . ,child-stobj)
      (:child-accessor . ,child-accessor)
      (:child-updater . ,child-updater)
      (:exec-fieldname . ,exec-fieldname)
      (:exec-accessor . ,exec-accessor)
      (:exec-updater . ,exec-updater)
      ;; Functions :child-exec-accessor and :child-exec-updater are generated by defrstobj.
      (:child-exec-accessor . ,child-exec-accessor)
      (:child-exec-updater  . ,child-exec-updater)
      (:length . ,length)
      (:accessor . ,accessor)
      (:logic-accessor . ,logic-accessor)
      (:updater . ,updater)
      (:logic-updater . ,logic-updater)
      (:field-key . ,field-key))))


(defun parse-defrstobj-fields (fields x)
  (if (atom fields)
      nil
    (cons (parse-defrstobj-field (car fields) x)
          (parse-defrstobj-fields (cdr fields) x))))

(defconst *defrstobj-field-keys*
  (strip-cars (parse-defrstobj-field '(foo) nil)))


(defconst *defrstobj-user-keys*
  (set-difference-eq *defrstobj-keys*
                     '(:name :fields)))

(make-event
 (std::da-make-binder-gen
  'rstobj-field
  (kwd-alist-field-accessor-alist *defrstobj-field-keys*)))



(defun parse-defrstobj (x)
  (b* ((name (car x))
       ((unless (symbolp name))
        (er hard? 'parse-defrstobj "Must start with a name (symbol)."))
       ((mv kwd-alist fields)
        (std::extract-keywords 'parse-defrstobj
                               *defrstobj-user-keys*
                               (cdr x) nil))
       (mksym-pkg (or (cdr (assoc :pkg-sym kwd-alist))
                      name))
       (recname-look (assoc :recname kwd-alist))
       (recname (if recname-look
                    (cdr recname-look)
                  (mksym name 'rec)))
       (elem-p-look (assoc :elem-p kwd-alist))
       (elem-p (if elem-p-look (cdr elem-p-look)
                 (mksym name '-elem-p)))
       (elem-fix-look (assoc :elem-fix kwd-alist))
       (elem-fix (if elem-fix-look (cdr elem-fix-look)
                   (mksym name '-elem-fix)))
       (elem-default-look (assoc :elem-default kwd-alist))
       (elem-default (if elem-default-look (cdr elem-default-look)
                       (mksym name '-elem-default)))
       (concrete-stobj-look (assoc :concrete-stobj kwd-alist))
       (concrete-stobj (if concrete-stobj-look (cdr concrete-stobj-look)
                         (mksym name '$c)))
       (logic-stobj-look (assoc :logic-stobj kwd-alist))
       (logic-stobj (if logic-stobj-look (cdr logic-stobj-look)
                      (mksym name '$a)))
       (recognizer-look (assoc :recognizer kwd-alist))
       (recognizer (if recognizer-look (cdr recognizer-look)
                     (mksym name 'p)))
       (logic-recognizer-look (assoc :logic-recognizer kwd-alist))
       (logic-recognizer (if logic-recognizer-look (cdr logic-recognizer-look)
                           (mksym logic-stobj 'p)))
       (creator-look (assoc :creator kwd-alist))
       (creator (if creator-look (cdr creator-look)
                  (mksym 'create- name)))
       (logic-creator-look (assoc :logic-creator kwd-alist))
       (logic-creator (if logic-creator-look (cdr logic-creator-look)
                        (mksym 'create- logic-stobj)))
       (accessor-template (std::getarg :accessor-template
                                       '(get- x) kwd-alist))
       (updater-template (std::getarg :updater-template
                                      '(set- x) kwd-alist))
       (accessor-look (assoc :accessor kwd-alist))
       (accessor (if accessor-look (cdr accessor-look)
                   (mksym-list (subst name 'x accessor-template))))
       (updater-look (assoc :updater kwd-alist))
       (updater (if updater-look (cdr updater-look)
                  (mksym-list (subst name 'x updater-template))))
       (enable (cdr (assoc :enable kwd-alist)))
       (tmp-x `((:name . ,name)
                (:recname . ,recname)
                (:inline . ,(std::getarg :inline t kwd-alist))
                (:non-memoizable . ,(std::getarg :non-memoizable nil kwd-alist))
                (:pkg-sym . ,mksym-pkg)
                (:elem-p . ,elem-p)
                (:elem-fix . ,elem-fix)
                (:elem-default . ,elem-default)
                (:concrete-stobj . ,concrete-stobj)
                (:logic-stobj . ,logic-stobj)
                (:recognizer . ,recognizer)
                (:logic-recognizer . ,logic-recognizer)
                (:creator . ,creator)
                (:logic-creator . ,logic-creator)
                (:accessor . ,accessor)
                (:updater . ,updater)
                (:accessor-template . ,accessor-template)
                (:updater-template . ,updater-template)
                (:enable . ,enable)))
       (fields (parse-defrstobj-fields fields tmp-x)))
    (cons (cons :fields fields) tmp-x)))

(defun rstobj-concrete-recognizer (x)
  (b* (((rstobj x)))
    (acl2::defstobj-fnname x.concrete-stobj :recognizer :top nil)))

(defun rstobj-concrete-creator (x)
  (b* (((rstobj x)))
    (acl2::defstobj-fnname x.concrete-stobj :creator :top nil)))

(defun rstobj-field-defconst (field)
  (b* (((rstobj-field field)))
    (acl2::defconst-name field.exec-accessor)))

;; (defun rstobj-orig-theory (x)
;;   (b* (((rstobj x))
;;        (mksym-pkg x.pkg-sym))
;;     (mksym x.name '-orig-theory)))

(defun rstobj-start-label (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym))
    (mksym x.name '-start)))



(defun rstobj-concrete-stobj-field (field)
  (b* (((rstobj-field field)))
    `(,field.exec-fieldname :type ,field.stobj-type
                            ,@(if field.child-stobj
                                  nil
                                `(:initially ,field.initially)))))

(defun rstobj-concrete-stobj-fields (fields)
  (if (atom fields)
      nil
    (cons (rstobj-concrete-stobj-field (car fields))
          (rstobj-concrete-stobj-fields (cdr fields)))))

(defun rstobj-concrete-stobj-def (x)
  (b* (((rstobj x)))
    `(defstobj ,x.concrete-stobj
       ,@(rstobj-concrete-stobj-fields x.fields)
       :inline ,x.inline
       :non-memoizable ,x.non-memoizable)))

(defun rstobj-concrete-stobj-field-child-stobj-accessor/updater-def (x.concrete-stobj field)
  (b* (((rstobj-field field)))
    `(progn
       (defun ,field.child-exec-accessor (,@(and field.arrayp `(i)) ,x.concrete-stobj)
         (declare (xargs :guard ,@(if field.arrayp
                                      `((and (integerp i)
                                             (<= 0 i)
                                             (< i ,field.length)))
                                    `(t))
                         :stobjs ,x.concrete-stobj))
         (stobj-let
          ((,field.child-stobj (,field.exec-accessor ,x.concrete-stobj)))
          (val)
          (,field.child-accessor ,@(and field.arrayp `(i)) ,field.child-stobj)
          val))
       (defun ,field.child-exec-updater (,@(and field.arrayp `(i)) v ,x.concrete-stobj)
         (declare (xargs :guard (and
                                 ,(subst 'v 'x field.pred)
                                 ,@(and field.arrayp
                                        `((integerp i)
                                          (<= 0 i)
                                          (< i ,field.length))))
                         :stobjs ,x.concrete-stobj))
         (stobj-let
          ((,field.child-stobj (,field.exec-accessor ,x.concrete-stobj)))
          (,field.child-stobj)
          (,field.child-updater ,@(and field.arrayp `(i)) v ,field.child-stobj)
          ,x.concrete-stobj)))))


(defun rstobj-concrete-stobj-field-child-stobj-accessor/updater-defs (x.concrete-stobj fields)
  (if (atom fields)
      nil
    (b* (((rstobj-field field) (car fields))
         (rest (rstobj-concrete-stobj-field-child-stobj-accessor/updater-defs x.concrete-stobj (cdr fields))))
      (if field.child-stobj
          (cons (rstobj-concrete-stobj-field-child-stobj-accessor/updater-def x.concrete-stobj (car fields))
                rest)
        rest))))

(defun rstobj-child-stobj-concrete-accessor/updater-defs (x)
  (b* (((rstobj x)))
    (rstobj-concrete-stobj-field-child-stobj-accessor/updater-defs x.concrete-stobj x.fields)))

(defun rstobj-elem-p-case (field)
  (b* (((rstobj-field field)))
    `(,field.field-key ,field.pred)))

(defun rstobj-elem-p-cases (fields)
  (if (Atom fields)
      '((otherwise t))
    (cons (rstobj-elem-p-case (car fields))
          (rstobj-elem-p-cases (cdr fields)))))

(defun rstobj-elem-p-def (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym)
       (cases (rstobj-elem-p-cases x.fields)))
    `(progn (defun ,x.elem-p (key x)
              (declare (xargs :guard t))
              (case key
                . ,cases))
            (defthm ,(mksym x.elem-p '-opener)
              (implies (syntaxp (quotep k))
                       (equal (,x.elem-p k x)
                              (case k
                                . ,cases))))
            (in-theory (disable ,x.elem-p))
            (defun ,(mksym x.elem-p '-top) (key x)
              (declare (xargs :guard t))
              (,x.elem-p (ec-call (car key)) x)))))




(defun rstobj-elem-fix-case (field)
  (b* (((rstobj-field field)))
    `(,field.field-key ,field.fix)))

(defun rstobj-elem-fix-cases (fields)
  (if (Atom fields)
      '((otherwise x))
    (cons (rstobj-elem-fix-case (car fields))
          (rstobj-elem-fix-cases (cdr fields)))))

(defun rstobj-elem-fix-def (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym)
       (cases (rstobj-elem-fix-cases x.fields)))
    `(progn (defun ,x.elem-fix (key x)
              (declare (xargs :guard t))
              (case key
                    . ,cases))
            (defthm ,(mksym x.elem-fix '-opener)
              (implies (syntaxp (quotep k))
                       (equal (,x.elem-fix k x)
                              (case k
                                . ,cases))))
            (defthm ,(mksym x.elem-p '-of- x.elem-fix)
              (,x.elem-p k (,x.elem-fix k x))
              :hints ((and stable-under-simplificationp
                           '(:in-theory (enable ,x.elem-p)))))
            (defthm ,(mksym x.elem-fix '-when- x.elem-p)
              (implies (,x.elem-p k x)
                       (equal (,x.elem-fix k x) x))
              :hints ((and stable-under-simplificationp
                           '(:in-theory (enable ,x.elem-p)))))
            (in-theory (disable ,x.elem-fix))
            (defun ,(mksym x.elem-fix '-top) (key x)
              (declare (xargs :guard t))
              (,x.elem-fix (ec-call (car key)) x)))))


(defun rstobj-elem-default-case (field)
  (b* (((rstobj-field field)))
    `(,field.field-key ',field.initially)))

(defun rstobj-elem-default-cases (fields)
  (if (Atom fields)
      '((otherwise nil))
    (cons (rstobj-elem-default-case (car fields))
          (rstobj-elem-default-cases (cdr fields)))))


(defun rstobj-elem-default-def (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym)
       (cases (rstobj-elem-default-cases x.fields)))
    `(progn (defun ,x.elem-default (key)
              (declare (xargs :guard t))
              (case key
                . ,cases))
            (defthm ,(mksym x.elem-default '-opener)
              (implies (syntaxp (quotep k))
                       (equal (,x.elem-default k)
                              (case k
                                . ,cases))))
            (defthm ,(mksym x.elem-p '-of- x.elem-default)
              (,x.elem-p k (,x.elem-default k))
              :hints ((and stable-under-simplificationp
                           '(:in-theory (enable ,x.elem-p)))))
            (in-theory (disable ,x.elem-default))
            (defun ,(mksym x.elem-default '-top) (key)
              (declare (xargs :guard t))
              (,x.elem-default (ec-call (car key)))))))


(defun rstobj-record-def (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym))
    `(def-multityped-record ,x.recname
       :elem-p (,(mksym x.elem-p '-top) k x)
       :elem-fix (,(mksym x.elem-fix '-top) k x)
       :elem-default (,(mksym x.elem-default '-top) k)
       :in-package-of ,x.pkg-sym)))

(defun rstobj-elem-p-of-accessor-thm (field x)
  (b* (((rstobj-field field))
       ((rstobj x))
       (mksym-pkg x.pkg-sym)
       ((when (eq field.pred t))
        nil))
    `((make-event
       '(:or (defthm ,(mksym 'elem-p-of- x.accessor '- field.fieldname)
               ,(subst `(,x.accessor ,field.field-key i ,x.logic-stobj)
                       'x field.pred)
               :hints (("goal" :use ((:instance ,(mksym x.elem-p '-of- x.accessor)
                                                (fld ,field.field-key)))
                        :in-theory (disable ,(mksym x.elem-p '-of- x.accessor)))))
             (make-event
              (prog2$ (cw "*** NOTE: Failed to prove rewrite rule stating that ~x0 satisfies ~x1 for field ~x2.~%"
                          ',x.accessor ',field.pred ',field.field-key)
                      '(value-triple :skipped))))))))

(defun rstobj-elem-p-of-accessor-thms (fields x)
  (if (atom fields)
      nil
    (append (rstobj-elem-p-of-accessor-thm (car fields) x)
            (rstobj-elem-p-of-accessor-thms (cdr fields) x))))


(defun rstobj-accessor/updater-defs (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym))
    `((defun ,x.accessor (fld index ,x.logic-stobj)
        (declare (xargs :guard t))
        (,(mksym x.recname '-get) (cons fld index) ,x.logic-stobj))
      (defun ,x.updater (fld index val ,x.logic-stobj)
        (declare (xargs :guard t))
        (,(mksym x.recname '-set) (cons fld index) val ,x.logic-stobj))

      (defthm ,(mksym x.elem-p '-of- x.accessor)
        (,x.elem-p fld (,x.accessor fld i ,x.logic-stobj))
        :hints (("goal" :use ((:instance ,(mksym 'elem-p-of- x.recname '-get)
                               (a (cons fld i)) (x ,x.logic-stobj)))
                 :in-theory (disable ,(mksym 'elem-p-of- x.recname '-get)))))

      ,@(rstobj-elem-p-of-accessor-thms x.fields x)

      (defthm ,(mksym x.accessor '-of-nil)
        (equal (,x.accessor fld i nil)
               (,x.elem-default fld)))

      (defthm ,(mksym x.recname '-bad-part-of- x.updater)
        (equal (,(mksym x.recname '-bad-part) (,x.updater fld i val ,x.logic-stobj))
               (,(mksym x.recname '-bad-part) ,x.logic-stobj)))

      (defthm ,(mksym x.accessor '-of- x.updater '-intra-field)
        (equal (,x.accessor fld i (,x.updater fld j v ,x.logic-stobj))
               (if (equal i j)
                   (,x.elem-fix fld v)
                 (,x.accessor fld i ,x.logic-stobj))))

      (defthm ,(mksym x.accessor '-of- x.updater '-inter-field)
        (implies (case-split (not (equal fld1 fld2)))
                 (equal (,x.accessor fld2 i2 (,x.updater fld1 i1 v ,x.logic-stobj))
                        (,x.accessor fld2 i2 ,x.logic-stobj))))

      (defthm ,(mksym x.updater '- x.updater '-shadow-writes)
        (equal (,x.updater fld i v2 (,x.updater fld i v1 ,x.logic-stobj))
               (,x.updater fld i v2 ,x.logic-stobj)))

      (defthm ,(mksym x.updater '- x.updater '-intra-field-arrange-writes)
        (implies (not (equal (nfix i1) (nfix i2)))
                 (equal (,x.updater fld i2 v2 (,x.updater fld i1 v1 ,x.logic-stobj))
                        (,x.updater fld i1 v1 (,x.updater fld i2 v2 ,x.logic-stobj))))
        :rule-classes ((:rewrite :loop-stopper ((i2 i1)))))

      (defthm ,(mksym x.updater '- x.updater '-inter-field-arrange-writes)
        (implies (not (equal fld1 fld2))
                 (equal (,x.updater fld2 i2 v2 (,x.updater fld1 i1 v1 ,x.logic-stobj))
                        (,x.updater fld1 i1 v1 (,x.updater fld2 i2 v2 ,x.logic-stobj))))
        :rule-classes ((:rewrite :loop-stopper ((fld2 fld1)))))

      (defthm ,(mksym x.updater '-of- x.accessor)
        (equal (,x.updater fld i (,x.accessor fld i ,x.logic-stobj) ,x.logic-stobj)
               ,x.logic-stobj))

      (in-theory (disable ,x.accessor ,x.updater)))))


(defun rstobj-logic-accessor-def (field x)
  (b* (((rstobj-field field))
       ((rstobj x))
       ;; (mksym-pkg x.pkg-sym)
       )
    `(defun ,field.logic-accessor (,@(and field.arrayp
                                          '(idx))
                                     ,x.logic-stobj)
       (declare (xargs :guard ,(if field.arrayp
                                   `(and (natp idx)
                                         (< idx ,field.length))
                                 t)))
       (,x.accessor
        ,field.field-key
        ,(and field.arrayp
              '(nfix idx))
        ,x.logic-stobj))))

(defun rstobj-logic-accessor-defs (fields x)
  (if (atom fields)
      nil
    (cons (rstobj-logic-accessor-def (car fields) x)
          (rstobj-logic-accessor-defs (cdr fields) x))))

(defun rstobj-logic-updater-def (field x)
  (b* (((rstobj-field field))
       ((rstobj x))
       ;; (mksym-pkg x.pkg-sym)
       )
    `(defun ,field.logic-updater (,@(and field.arrayp
                                          '(idx))
                                    v
                                     ,x.logic-stobj)
       (declare (xargs :guard ,(if field.arrayp
                                   `(and (natp idx)
                                         (< idx ,field.length)
                                         ,(subst 'v 'x field.pred))
                                 (subst 'v 'x field.pred))))
       (,x.updater
        ,field.field-key
        ,(and field.arrayp
              '(nfix idx))
        v
        ,x.logic-stobj))))

(defun rstobj-logic-updater-defs (fields x)
  (if (atom fields)
      nil
    (cons (rstobj-logic-updater-def (car fields) x)
          (rstobj-logic-updater-defs (cdr fields) x))))



(defun rstobj-field-array-corr-name (field x)
  (b* (((rstobj-field field))
       ((rstobj x))
       (mksym-pkg x.pkg-sym))
    (mksym x.name '- field.fieldname '-corr)))

(defun rstobj-field-array-corr-def (field x)
  (b* (((rstobj-field field))
       ((unless field.arrayp) nil)
       ((rstobj x))
       (mksym-pkg x.pkg-sym)
       (name (rstobj-field-array-corr-name field x))
       (field-index (rstobj-field-defconst field)))
    `((defun-sk ,name (,x.concrete-stobj ,x.logic-stobj)
        (forall idx
                (implies (and (natp idx) (< idx ,field.length))
                         (equal ,(if field.child-stobj
                                     `(,field.child-accessor idx (nth ,field-index ,x.concrete-stobj))
                                   `(nth idx (nth ,field-index ,x.concrete-stobj)))
                                (,x.accessor
                                 ,field.field-key (nfix idx)
                                 ,x.logic-stobj))))
        :rewrite :direct)
      (in-theory (disable ,name))
      (defthm ,(mksym name '-of-update-other)
       (implies (and (,name ,x.concrete-stobj ,x.logic-stobj)
                     (not (equal (nfix field-index2) ,field-index))
                     (not (equal field-key2 ,field.field-key)))
                (,name
                 (update-nth field-index2 new-field2 ,x.concrete-stobj)
                 (,x.updater field-key2 idx val ,x.logic-stobj)))
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause)))))))

     (defthm ,(mksym name '-of-update)
       (implies (and (,name ,x.concrete-stobj ,x.logic-stobj)
                     ,(subst 'val 'x field.pred)
                     (natp idx) (< idx ,field.length))
                (,name
                 (update-nth ,field-index
                             ,(if field.child-stobj
                                  `(,field.child-updater idx val (nth ,field-index ,x.concrete-stobj))
                                `(update-nth idx val (nth ,field-index ,x.concrete-stobj)))
                             ,x.concrete-stobj)
                 (,x.updater ,field.field-key idx val ,x.logic-stobj)))
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))))))))))

(defun rstobj-field-array-corr-defs (fields x)
  (if (atom fields)
      nil
    (append (rstobj-field-array-corr-def (car fields) x)
            (rstobj-field-array-corr-defs (cdr fields) x))))

(defun rstobj-field-array-corr-names (fields x)
  (b* (((when (atom fields)) nil)
       ((rstobj-field field) (car fields))
       ((unless field.arrayp)
        (rstobj-field-array-corr-names (cdr fields) x)))
    (cons (rstobj-field-array-corr-name (car fields) x)
          (rstobj-field-array-corr-names (cdr fields) x))))

(defun rstobj-field-corr (field x)
  (b* (((rstobj-field field))
       ((rstobj x))
       ;; (mksym-pkg x.pkg-sym)
       ((when field.arrayp)
        `(,(rstobj-field-array-corr-name field x)
          ,x.concrete-stobj ,x.logic-stobj)))
    `(equal (,field.logic-accessor ,x.logic-stobj)
            (,(or field.child-exec-accessor field.exec-accessor)
             ,x.concrete-stobj))))

(defun rstobj-fields-corr (fields x)
  (if (atom fields)
      nil
    (cons (rstobj-field-corr (car fields) x)
          (rstobj-fields-corr (cdr fields) x))))

(defun rstobj-corr-name (x)
  (b* (((rstobj x))
       (mksym-pkg x.pkg-sym))
    (mksym x.name '-corr)))

(defun rstobj-corr-def (x)
  (b* (((rstobj x))
       (corr-name (rstobj-corr-name x)))
    `((defun-nx ,corr-name (,x.concrete-stobj ,x.logic-stobj)
        (and . ,(rstobj-fields-corr x.fields x)))
      (in-theory (disable (,corr-name))))))


(defun rstobj-exports-field (field)
  (b* (((rstobj-field field)))
    `((,field.accessor :logic ,field.logic-accessor :exec ,(or field.child-exec-accessor field.exec-accessor))
      (,field.updater :logic ,field.logic-updater :exec ,(or field.child-exec-updater field.exec-updater)))))

(defun rstobj-exports (fields)
  (if (atom fields)
      nil
    (append (rstobj-exports-field (car fields))
            (rstobj-exports (cdr fields)))))


(defun rstobj-defabsstobj (x)
  (b* (((rstobj x)))
    `(acl2::defabsstobj-events ,x.name
       :foundation ,x.concrete-stobj
       :corr-fn ,(rstobj-corr-name x)
       :recognizer (,x.recognizer :logic ,x.logic-recognizer :exec ,(rstobj-concrete-recognizer x))
       :creator (,x.creator :logic ,x.logic-creator :exec ,(rstobj-concrete-creator x))
       :exports ,(rstobj-exports x.fields))))

;; (defun rstobj-@!-def (field x)
;;   (b* (((rstobj-field field))
;;        ((rstobj x))
;;        (mksym-pkg x.pkg-sym))
;;     `((defun-inline ,(mksym '! field.fieldname) (,@(and field.arrayp '(i))
;;                                                     v ,x.name)
;;         (declare (xargs :guard ,(if field.arrayp
;;                                     `(and (natp i)
;;                                           (< i ,field.length)
;;                                           ,(subst 'v 'x field.pred))
;;                                   (subst 'v 'x field.pred))))
;;         (mbe :logic (,x.updater ,field.field-key
;;                                 ,@(and field.arrayp '(i))
;;                                 v ,x.name)
;;              :exec (,field.updater ,@(and field.arrayp '(i))
;;                                    v ,x,name)))
;;       (defun-inline ,(mksym '@ field.fieldname) (,@(and field.arrayp '(i))
;;                                                     ,x.name)
;;         (declare (xargs :guard ,(if field.arrayp
;;                                     `(and (natp i)
;;                                           (< i ,field.length))
;;                                   t)))
;;         (mbe :logic (,x.accessor ,field.field-key
;;                                  ,@(and field.arrayp '(i)) ,x.name)
;;              :exec (,field.accessor ,@(and field.arrayp '(i)) ,x,name))))))

;; (defun rstobj-@!-defs (fields x)
;;   (if (atom fields)
;;       nil
;;     (append (rstobj-@!-def (car fields) x)
;;             (rstobj-@!-defs (cdr fields) x))))




(defun defrstobj-fn (args)
  (b* (((rstobj x) (parse-defrstobj args))
       (mksym-pkg x.pkg-sym))
    `(encapsulate nil
       (local (deflabel ,(rstobj-start-label x)))
       ,(rstobj-concrete-stobj-def x)
       ,@(rstobj-child-stobj-concrete-accessor/updater-defs x)

       ,(rstobj-elem-p-def x)
       ,(rstobj-elem-fix-def x)
       ,(rstobj-elem-default-def x)

       ,(rstobj-record-def x)

       (local (in-theory (union-theories
                          ,x.enable
                          (union-theories
                           (union-theories
                            (theory 'minimal-theory)
                            '(acl2::natp-compound-recognizer
                              nth-update-nth
                              cons-equal
                              acl2::nfix-when-natp
                              (nfix) (natp)
                              car-cons cdr-cons
                              (make-list-ac)
                              (nth) (cons) (len)
                              update-nth-array))
                           (set-difference-theories
                            (current-theory :here)
                            (current-theory ',(rstobj-start-label x)))))))

       ,@(rstobj-accessor/updater-defs x)

       ,@(rstobj-logic-accessor-defs x.fields x)
       ,@(rstobj-logic-updater-defs x.fields x)

       (defun ,x.logic-recognizer (,x.logic-stobj)
          (declare (xargs :guard t))
          (not (,(mksym x.recname '-bad-part) ,x.logic-stobj)))

       (defun ,x.logic-creator ()
         (declare (xargs :guard t))
         nil)

       (local
        (progn
          (in-theory (disable nth update-nth acl2::nth-when-zp nth-add1))
          ,@(rstobj-field-array-corr-defs x.fields x)

          ,@(rstobj-corr-def x)

          (set-default-hints
           '((and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    (and (consp lit)
                         (member-eq (car lit) ',(rstobj-field-array-corr-names x.fields x))
                         `(:expand (,lit)))))))

          (in-theory (e/d (nth-when-all-equal nth-of-cons (all-equal) (zp))))))

       ,(rstobj-defabsstobj x)

       )))

(defmacro defrstobj (&rest args)
  (defrstobj-fn args))


(logic)

(local (include-book "centaur/bitops/ihsext-basics" :Dir :System))
(local
 (defrstobj myst
   (u32-scalar :type (unsigned-byte 32) :initially 0 :fix (ec-call (acl2::loghead$inline 32 x)))
   (u32-array :type (array (unsigned-byte 32) (16)) :initially 5 :fix (acl2::loghead 32 (ifix x)))
   (nat-scalar :type (integer 0 *) :initially 6 :fix (nfix x))
   (nat-array :type (array (integer 0 *) (12)) :initially 8 :fix (nfix x))))

(local
 (defrstobj myst2
   (myst2-u32-scalar :type (unsigned-byte 32) :initially 0 :fix (ec-call (acl2::loghead$inline 32 x))
                     :field-key :u32-scalar)
   (myst2-u32-array :type (array (unsigned-byte 32) (16)) :initially 5 :fix (acl2::loghead 32 (ifix x))
                    :field-key :u32-array)
   (myst2-nat-scalar :type (integer 0 *) :initially 6 :fix (nfix x)
                     :field-key :nat-scalar)
   (myst2-nat-array :type (array (integer 0 *) (12)) :initially 8 :fix (nfix x)
                    :field-key :nat-array)
   (myst2-untyped-scalar :type t :initially "foo" :field-key :untyped-scalar)
   (myst2-untyped-array :type (array t (15)) :initially "bar" :field-key :untyped-array)
   :accessor-template (@ x)
   :updater-template (! x)))

(local
 (encapsulate
   ()
   (defstobj mem
     (arr :type (array (unsigned-byte 8) (10))
          :initially 0)
     :renaming ((arri read-mem)
                (update-arri write-mem)))

   (defthm read-mem-from-create-mem
     (implies (and (natp i)
                   (< i 10))
              (equal (read-mem i (create-mem)) 0))
     :hints (("Goal" :in-theory (e/d ()
                                     (acl2::make-list-ac-removal
                                      make-list-ac
                                      (make-list-ac))))))
   (defthm read-mem-over-write-mem
     (implies (and (unsigned-byte-p 8 v)
                   (natp i) (natp j)
                   (< i 10)
                   (< j 10))
              (equal (read-mem i (write-mem j v mem))
                     (if (equal i j)
                         v
                       (read-mem i mem)))))

   (in-theory (e/d () (read-mem write-mem)))))

(local
 (defrstobj myst3
   (child :type (array (unsigned-byte 8) (10))
          :initially 0
          :fix (acl2::loghead$inline 8 (ifix x))
          :child-stobj mem
          :child-accessor read-mem
          :child-updater write-mem)
   (u10-scalar :type (unsigned-byte 10) :initially 0 :fix (ec-call (acl2::loghead$inline 10 x)))
   :enable '(read-mem-over-write-mem
             read-mem-from-create-mem)))
