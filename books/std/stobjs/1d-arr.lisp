; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "STOBJS")
(include-book "absstobjs")
(include-book "xdoc/str" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)

;; BOZO might move this somewhere more sensible.
;; This differs from Common Lisp typep in that it's a macro, and type must be a
;; plain type-spec (it is not evaluated).
(defmacro typep$ (x type)
  (declare (xargs :guard (acl2::translate-declaration-to-guard type 'var nil)))
  (acl2::translate-declaration-to-guard type x nil))


(defxdoc def-1d-arr
  :parents (std/stobjs)
  :short "Defines a @(see abstract-stobj) that logically just appears to be a
typed list but is implemented as an array."

  :long "<p>Def-1d-arr produces an @(see abstract-stobj) and associated
@('get'), @('set'), @('resize'), and @('length') functions.  Logically the
stobj just looks like an (optionally) typed list.  But for execution, these
functions are stobj array operations.</p>

<p>How is this any better than just using @(see defstobj) to define a new stobj
with an array field?  With a regular @('defstobj'), the stobj is logically
viewed as a singleton list whose @('car') holds the contents.  With
@('def-1d-arr') this extra layer goes away: the stobj itself, rather than its
@('car'), looks like the list of elements.</p>

<p>This difference is slight, but it can help to simplify reasoning, e.g., it
can make @(see congruence)-based reasoning via @(see equivalence) relations
like @(see acl2::list-equiv) and @(see acl2::set-equiv) easier to apply to your
array, and can also make it easier to use proof strategies like @(see
acl2::equal-by-nths).</p>

<h3>Example</h3>

<p>The following defines a bit array named @(see acl2::bitarr).</p>

@({
    (def-1d-arr bitarr          ;; Stobj name
      :slotname    bit          ;; Base name for accessor functions
      :pred        bitp         ;; Element type (optional)
      :type-decl   bit          ;; Element type-spec (optional)
      :fix         bfix         ;; Element fixing function (optional)
      :default-val 0            ;; Element default value (for resizing)
      :parents (std/stobjs))    ;; XDOC parent topics
})


<h3>Keyword Options</h3>

<dl>

<dt>@(':slotname') and @(':pkg-sym')</dt>

<dd>The @(':slotname') influences the names of the array get, set, length, and
resize functions.  In the example above, using @('bit') results in functions
named @('get-bit'), @('set-bit'), @('bits-length'), and @('resize-bits').
Default: @('<arrname>val').</dd>

<dd>The @(':pkg-sym'), if given, determines the package in which any newly
created symbols will be interned.  It defaults to the array name.</dd>


<dt>@(':pred')</dt>

<dd>This can be used to restrict the types of elements that can be put into the
array.  It impacts the array recognizer's definition and the guard of the array
functions.  The default is @('nil'), meaning that there are no restrictions and
any kind of element can be put into the array.</dd>


<dt>@(':default-val')</dt>

<dd>This gives the default array element for resizing, i.e., the
@(':initially') argument to the underlying @(see stobj).  This is often
necessary when you provide a restricted @(':pred'), because the default value
needs to satisfy the predicate.</dd>


<dt>@(':type-decl')</dt>

<dd>This provides a Common Lisp @(see acl2::type-spec) declaration for the
array element's type.  It primarily affects memory efficiency and performance.
It must sensibly agree with the given @('pred').</dd>


<dt>@(':fix')</dt>

<dd>Optional, requires a compatible @(':pred').  This alters the logical
definition of the getting function so that it always produces a result of the
correct type.  For example, by using @(':fix bfix') above, @('get-bit') will be
defined as @('(bit-fix (nth i bitarr))') instead of just a call of @(see
nth).</dd>

<dt>@(':parents'), @(':short'), @(':long')</dt>

<dd>These options are as in @(see defxdoc).  Note that you typically don't need
to give @(':short') or @(':long') descriptions because reasonable boilerplate
documentation can be generated automatically.</dd>

</dl>")


(defconst *def-1d-arr-events*
  '(encapsulate
     nil
     (local
      (progn
        (include-book "data-structures/list-defthms" :dir :system)
        (in-theory (enable nth update-nth resize-list))
        (local (in-theory (disable acl2::resize-list-when-empty)))

        (:@ :fix
         (def-universal-equiv 1d-arr-tmp-equiv
           :equiv-terms ((equal (_fix_ acl2::x)))))

        ;; (def-universal-equiv 1d-arr-tmp-list-equiv
        ;;   :qvars (i)
        ;;   :equiv-terms ((1d-arr-tmp-equiv (nth i x))))

        ;; (defcong 1d-arr-tmp-list-equiv 1d-arr-tmp-equiv (nth i x) 2
        ;;   :hints(("Goal" :in-theory (e/d (1d-arr-tmp-list-equiv-necc)
        ;;                                  (1d-arr-tmp-equiv)))))

        ;; (defcong 1d-arr-tmp-list-equiv 1d-arr-tmp-list-equiv (update-nth i v x) 3
        ;;   :hints((and stable-under-simplificationp
        ;;               `(:expand (,(car (last clause)))))))

        ;; (defcong 1d-arr-tmp-equiv 1d-arr-tmp-list-equiv (update-nth i v x) 2
        ;;   :hints((and stable-under-simplificationp
        ;;               `(:expand (,(car (last clause)))))))

        ;; (in-theory (enable 1d-arr-tmp-list-equiv))

        (:@ :pred
         (defun 1d-arr-tmp-listp (x)
           (if (atom x)
               (eq x nil)
             (and (:@ :pred (_pred_ (car x)))
                  (1d-arr-tmp-listp (cdr x)))))

         (defthm _pred_-nth-of-1d-arr-tmp-listp
           (implies (and (1d-arr-tmp-listp x)
                         (< (nfix n) (len x)))
                    (_pred_ (nth n x))))

         (defthm 1d-arr-tmp-listp-of-update-nth
          (implies (and (1d-arr-tmp-listp x)
                        (_pred_ v)
                        (<= (nfix n) (len x)))
                   (1d-arr-tmp-listp (update-nth n v x))))

         (defthm 1d-arr-tmp-listp-of-resize-list
           (implies (and (1d-arr-tmp-listp x)
                         (_pred_ default))
                    (1d-arr-tmp-listp (resize-list x n default)))
           :hints (("goal" :in-theory '(resize-list
                                        car-cons
                                        cdr-cons
                                        1d-arr-tmp-listp))))
           )))

     (defstobj _arrname_$c
       (_slotname_s$c :type (array _type-decl_
                                   (0))
                      :initially _default-val_
                      :resizable t)
       :inline t)

     (local
      (progn

        (defthm _slotname_s$cp-of-update-nth
          (implies (and (_slotname_s$cp x)
                        (typep$ v _type-decl_)
                        (<= (nfix n) (len x)))
                   (_slotname_s$cp (update-nth n v x))))

        (defthm _slotname_s$cp-of-resize-list
          (implies (and (_slotname_s$cp x)
                        (typep$ default _type-decl_))
                   (_slotname_s$cp (resize-list x n default)))
           :hints (("goal" :in-theory '(resize-list
                                        car-cons
                                        cdr-cons
                                        _slotname_s$cp))))))

     (defun _arrname_$ap (_arrname_$a)
       (declare (xargs :guard t :verify-guards t)
                (ignorable _arrname_$a))
       (:@ :pred
        (if (atom _arrname_$a)
            (eq _arrname_$a nil)
          (and (_pred_ (car _arrname_$a))
               (_arrname_$ap (cdr _arrname_$a)))))
       (:@ (not :pred)
        (true-listp _arrname_$a)))

     (:@ :pred
      (local (defthm _arrname_$ap-rewrite-to-1d-arr-tmp-listp
               (equal (_arrname_$ap x)
                      (1d-arr-tmp-listp x)))))

     (defun create-_arrname_$a ()
       (declare (xargs :guard t :verify-guards t))
       nil)

     (defun _slotname_s$a-length (_arrname_$a)
       (declare (xargs :guard (_arrname_$ap _arrname_$a)
                       :verify-guards t))
       (len _arrname_$a))

     (defun resize-_slotname_s$a (i _arrname_$a)
       (declare (xargs :guard (_arrname_$ap _arrname_$a)
                       :verify-guards t))
       (resize-list _arrname_$a i '_default-val_))

     (defun _slotname_s$ai (i _arrname_$a)
       (declare (xargs :guard (and (_arrname_$ap _arrname_$a)
                                   (integerp i)
                                   (<= 0 i)
                                   (< i (_slotname_s$a-length _arrname_$a)))
                       :verify-guards t))
       (:@ :fix
        ;; outer ec-call supports fixing functions with guards
        ;; e.g. the following sort of implementation
        ;; (mbe :logic (if (foo-p a) a 'default-val) :exec a)
        (ec-call (_fix_ (ec-call (nth i _arrname_$a)))))
       (:@ (not :fix)
        (ec-call (nth i _arrname_$a))))

     (defun update-_slotname_s$ai (i v _arrname_$a)
       (declare (xargs :guard (and (_arrname_$ap _arrname_$a)
                                   (integerp i)
                                   (<= 0 i)
                                   (< i (_slotname_s$a-length _arrname_$a))
                                   (:@ :pred (_pred_ v))
                                   (typep$ v _type-decl_))
                       :verify-guards t))
       (ec-call (update-nth i
                            (:@ :fix (_fix_ v))
                            (:@ (not :fix) v)
                            _arrname_$a)))

     (local (defun-nx _arrname_$corr (_arrname_$c _arrname_$a)
              (equal _arrname_$a (nth 0 _arrname_$c))))

     (local (in-theory (disable nth resize-list
                                (_arrname_$corr))))

     ;; (local (set-default-hints
     ;;         '((and stable-under-simplificationp
     ;;                (let ((lit (car (last clause))))
     ;;                  (and (consp lit)
     ;;                       (eq (car lit) '1d-arr-tmp-list-equiv)
     ;;                       `(:expand (,lit))))))))

     ;; (local (defthm nths-equal-by-1d-arr-tmp-list-equiv
     ;;          (implies (and (1d-arr-tmp-list-equiv x y)
     ;;                        (:@ :pred (1d-arr-tmp-listp x))
     ;;                        (< (nfix i) (len x)))
     ;;                   (equal (equal (nth i x)
     ;;                                 (:@ :fix (_fix_ (nth i y)))
     ;;                                 (:@ (not :fix) (nth i y)))
     ;;                          t))
     ;;          :hints (("goal" :use 1d-arr-tmp-list-equiv-necc
     ;;                   :in-theory (e/d ((:@ :fix 1d-arr-tmp-equiv))
     ;;                                   (1d-arr-tmp-list-equiv-necc
     ;;                                    (:@ :fix
     ;;                                     1d-arr-tmp-list-equiv-implies-1d-arr-tmp-equiv-nth-2)
     ;;                                    (:@ (not :fix)
     ;;                                     1d-arr-tmp-list-equiv-implies-equal-nth-2)))
     ;;                   :do-not-induct t))))

     (local (in-theory (enable acl2::nth-of-resize-list-split)))

     (defabsstobj-events _arrname_
       :foundation _arrname_$c
       :recognizer (_arrname_p :exec _arrname_$cp :logic _arrname_$ap)
       :creator (create-_arrname_ :exec create-_arrname_$c :logic create-_arrname_$a)
       :corr-fn _arrname_$corr
       :exports ((_slotname_s-length :exec _slotname_s$c-length :logic _slotname_s$a-length)
                 (get-_slotname_ :exec _slotname_s$ci :logic _slotname_s$ai)
                 (set-_slotname_ :exec update-_slotname_s$ci :logic update-_slotname_s$ai)
                 (resize-_slotname_s :exec resize-_slotname_s$c :logic resize-_slotname_s$a)))

     (defxdoc _arrname_
       :parents _parents_
       :short (or _short_
                  (if '_pred_
                      (str::cat "Abstract stobj: logically this just represents a list of
                                 @('" (xdoc::full-escape-symbol '_pred_) "')s, but it is
                                 implemented as an array.")
                    (str::cat "Abstract stobj: logically this just represents
                               an untyped list, but it is implemented as an
                               array.")))
       :long (or _long_
                 "<p>This is a simple abstract stobj array, introduced by @(see
                  stobjs::def-1d-arr).</p>"))

     (defsection ext
       :extension _arrname_
       ;; Doing it this way, instead of putting it in the :long, lets you overwrite
       ;; the boilerplate :long above but still get the stobj definition.
       :long (str::cat "@(def " (xdoc::full-escape-symbol '_arrname_) ")"))

     ;; Hrmn, actually it's probably better NOT to generate docs for this, because
     ;; the user should never care about it.
     ;;
     ;; (defxdoc _arrname_p
     ;;   :parents (_arrname_)
     ;;   :short (str::cat "Recognizer for the @(see " (xdoc::full-escape-symbol '_arrname_) ") array.")
     ;;   :long (str::cat "<p>In guard obligations you will typically get to
     ;;                    assume this for free as a result of your
     ;;                    @('(declare (xargs :stobjs ...))') form.  In the logic,
     ;;                    this is just a basic list recognizer:</p>
     ;;                    @(def " (xdoc::full-escape-symbol '_arrname_$ap) ")"))

     (defxdoc _slotname_s-length
       :parents (_arrname_)
       :short (str::cat "Get the length of the @(see "
                        (xdoc::full-escape-symbol '_arrname_) ") array.")
       :long (str::cat "<p>In the execution this just gets the array length.  The
                        logical definition is just a wrapper for @(see len):</p>"
                        "@(def " (xdoc::full-escape-symbol '_slotname_s$a-length) ")"))

     (defxdoc get-_slotname_
       :parents (_arrname_)
       :short (str::cat "Read the @('n')th element of the @(see "
                        (xdoc::full-escape-symbol '_arrname_) ") array.")
       :long (str::cat "<p>In the execution this is an array access, but the logical
                        definition is just a thin wrapper for @(see nth):</p>
                        @(def " (xdoc::full-escape-symbol '_slotname_s$ai) ")"))

     (defxdoc set-_slotname_
       :parents (_arrname_)
       :short (str::cat "Modify the @('n')th element of the @(see "
                        (xdoc::full-escape-symbol '_arrname_) ") array.")
       :long (str::cat "<p>In the execution this is an array write, but the logical
                        definition is just a thin wrapper for @(see update-nth):</p>
                        @(def " (xdoc::full-escape-symbol 'update-_slotname_s$ai) ")"))

     (defxdoc resize-_slotname_s
       :parents (_arrname_)
       :short (str::cat "Change the length of the @(see "
                        (xdoc::full-escape-symbol '_arrname_) ") array.")
       :long (str::cat "<p>In the execution this resizes (to grow or shrink) the
                        underlying Common Lisp array.  The logical definition is
                        based on @(see resize-list):</p>
                        @(def " (xdoc::full-escape-symbol 'resize-_slotname_s$a) ")"))
     ))



(defun def-1d-arr-fn (arrname slotname
                              pred fix default-val
                              pkg-sym rename type-decl
                              parents short long)
  (declare (xargs :mode :program))
  (b* (((unless (and (symbolp arrname)
                     (not (keywordp arrname))))
        (er hard? 'def-1d-arr "Invalid array name: ~x0" arrname))
       ((unless (implies fix pred))
        (er hard? 'def-1d-arr "If :fix is supplied, :pred must also be"))
       (xdoc::mksym-package-symbol (or pkg-sym arrname))
       (slotname (or slotname (xdoc::mksym arrname 'val)))
       (type-decl (or type-decl `(satisfies ,pred)))
       (features (cond ((and pred fix) '(:pred :fix))
                       (pred '(:pred))))
       (symsubst `((_arrname_ . ,arrname)
                   (_slotname_ . ,slotname)
                   (_fix_ . ,fix)
                   (_pred_ . ,pred)
                   (_type-decl_ . ,type-decl)
                   (_default-val_ . ,default-val)
                   (_parents_ . ,parents)
                   (_short_ . ,short)
                   (_long_ . ,long)
                   ))
       (strsubst (acl2::tmpl-symbol-alist-to-str-alist symsubst))
       (symsubst (if fix symsubst
                   (cons '(1d-arr-tmp-equiv . equal) symsubst)))
       (tmpl
        (template-subst *def-1d-arr-events*
                        :features features
                        :atom-alist symsubst
                        :str-alist strsubst
                        :pkg-sym xdoc::mksym-package-symbol)))
    (if rename
        (sublis rename tmpl)
      tmpl)))


(defmacro def-1d-arr (arrname
                      &key
                      slotname
                      pred
                      fix
                      default-val
                      pkg-sym
                      rename
                      (type-decl 't)
                      (parents 'nil parents-p)
                      short
                      long)
  `(make-event
    (b* ((parents (if ,parents-p
                      ',parents
                    (or (xdoc::get-default-parents (w state))
                        '(acl2::undocumented))))
         (event (def-1d-arr-fn ',arrname ',slotname
                  ',pred ',fix ',default-val
                  ',pkg-sym ',rename ',type-decl
                  parents ',short ',long)))
      (value event))))

