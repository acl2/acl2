; Abstract stobj template for 1-dimensional typed arrays
; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "universal-equiv")
(include-book "absstobjs")
(include-book "tools/defmacfun" :dir :system)
(include-book "tools/templates" :dir :system)

;; BOZO might move this somewhere more sensible.
;; This differs from Common Lisp typep in that it's a macro, and type must be a
;; plain type-spec (it is not evaluated).
(defmacro typep$ (x type)
  (declare (xargs :guard (translate-declaration-to-guard type 'var nil)))
  (translate-declaration-to-guard type x nil))


(defconst *def-1d-arr-events*
  '(encapsulate
     nil
     (local
      (progn
        (include-book "data-structures/list-defthms" :dir :system)
        (in-theory (enable nth update-nth resize-list))
        (local (in-theory (disable RESIZE-LIST-WHEN-EMPTY)))

        (:@ :fix
         (def-universal-equiv 1d-arr-tmp-equiv
           :equiv-terms ((equal (_fix_ x)))))

        (def-universal-equiv 1d-arr-tmp-list-equiv
          :qvars (i)
          :equiv-terms ((1d-arr-tmp-equiv (nth i x))))

        (defcong 1d-arr-tmp-list-equiv 1d-arr-tmp-equiv (nth i x) 2
          :hints(("Goal" :in-theory (e/d (1d-arr-tmp-list-equiv-necc)
                                         (1d-arr-tmp-equiv)))))

        (defcong 1d-arr-tmp-list-equiv 1d-arr-tmp-list-equiv (update-nth i v x) 3
          :hints((and stable-under-simplificationp
                      `(:expand (,(car (last clause)))))))

        (defcong 1d-arr-tmp-equiv 1d-arr-tmp-list-equiv (update-nth i v x) 2
          :hints((and stable-under-simplificationp
                      `(:expand (,(car (last clause)))))))

        (:@ :pred
         (defun 1d-arr-tmp-listp (x)
           (if (atom x)
               t
             (and (_pred_ (car x))
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
                    (1d-arr-tmp-listp (resize-list x n default))))
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
                   (_slotname_s$cp (resize-list x n default))))))

     (defun _arrname_$ap (_arrname_$a)
       (declare (xargs :guard t :verify-guards t)
                (ignorable _arrname_$a))
       t)

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
              (and (:@ :pred (1d-arr-tmp-listp (nth 0 _arrname_$c)))
                   (equal (len _arrname_$a) (len (nth 0 _arrname_$c)))
                   (1d-arr-tmp-list-equiv _arrname_$a (nth 0 _arrname_$c)))))

     (local (in-theory (disable nth resize-list
                                (_arrname_$corr))))

     (local (set-default-hints
             '((and stable-under-simplificationp
                    (let ((lit (car (last clause))))
                      (and (consp lit)
                           (eq (car lit) '1d-arr-tmp-list-equiv)
                           `(:expand (,lit))))))))

     (local (defthm nths-equal-by-1d-arr-tmp-list-equiv
              (implies (and (1d-arr-tmp-list-equiv x y)
                            (:@ :pred (1d-arr-tmp-listp x))
                            (< (nfix i) (len x)))
                       (equal (equal (nth i x)
                                     (:@ :fix (_fix_ (nth i y)))
                                     (:@ (not :fix) (nth i y)))
                              t))
              :hints (("goal" :use 1d-arr-tmp-list-equiv-necc
                       :in-theory (e/d ((:@ :fix 1d-arr-tmp-equiv))
                                       (1d-arr-tmp-list-equiv-necc
                                        (:@ :fix
                                         1d-arr-tmp-list-equiv-implies-1d-arr-tmp-equiv-nth-2)
                                        (:@ (not :fix)
                                         1d-arr-tmp-list-equiv-implies-equal-nth-2)))
                       :do-not-induct t))))

     (local (in-theory (enable nth-of-resize-list-split)))

     (defabsstobj-events _arrname_
       :concrete _arrname_$c
       :recognizer (_arrname_p :exec _arrname_$cp :logic _arrname_$ap)
       :creator (create-_arrname_ :exec create-_arrname_$c :logic create-_arrname_$a)
       :corr-fn _arrname_$corr
       :exports ((_slotname_s-length :exec _slotname_s$c-length :logic _slotname_s$a-length)
                 (get-_slotname_ :exec _slotname_s$ci :logic _slotname_s$ai)
                 (set-_slotname_ :exec update-_slotname_s$ci :logic update-_slotname_s$ai)
                 (resize-_slotname_s :exec resize-_slotname_s$c :logic resize-_slotname_s$a)))))


(defxdoc def-1d-arr
  :parents (stobjs)
  :short "Defines a stobj containing an array of objects of a certain type, and
a convenient abstraction so that logically operations on it are just list
manipulations"

  :long "<p>Def-1d-arr produces an abstract stobj whose accessors/updaters are
list operations in the logic, but use fast array accesses to execute.</p>

<h2>Usage</h2>

<p>Example:</p>
@({
 (def-1d-arr :arrname swidgarr
      :slotname swidg
      :pred swidgp
      :fix swidg-fix
      :type-decl symbol
      :default-val the-default-swidg
      :pkg-sym xdoc::asdfs)
})

<p>The possible arguments are as follows:</p>
<ul>

 <li>@(':arrname') is the name of the abstract stobj that will be produced.  It
  defaults to @('<slotname>arr'), and @(':slotname') must be provided if
  @(':arrname') is not.</li>

 <li>@(':slotname') is the base for the names of the accessor functions.  It
  defaults to @('<arrname>val').  In this case, with slotname @('swidg'), the
  accessor functions will be:
  <ul>
   <li>@('swidgs-length')</li>
   <li>@('get-swidg')</li>
   <li>@('set-swidg')</li>
   <li>@('resize-swidgs')</li>
  </ul></li>

 <li>@(':pred') is a predicate recognizing elements of the desired type.  It
  defaults to @('nil'), in which case any object is accepted.</li>

 <li>@(':fix') is a fixing function of the desired type.  This may only be
supplied if @(':pred') is also given.  When the fixing function is supplied,
the logical definition of e.g. @('get-swidg') is @('(swidg-fix (nth i
swidgarr))'), which makes it trivial to show that array accesses always produce
elements of the correct type.</li>

  <li>@(':type-decl') is the type declaration that will be put on the base
stobj, primarily affecting performance.</li>

  <li>@(':default-val') gives the default array element for resizing (the
   @(':initially') argument to the stobj).</li>

  <li>@(':pkg-sym'), if given, determines the package in which any newly
created symbols will be interned.  If not given, @(':arrname') or
@(':slotname') are used instead.</li>

</ul>")


(deffunmac def-1d-arr (&key arrname
                            slotname
                            pred
                            fix
                            default-val
                            pkg-sym
                            rename
                            (type-decl 't))
  (declare (xargs :mode :program))
  (b* (((unless (or slotname arrname))
        (er hard? 'def-1d-arr
            "Either :slotname or :arrname keyword args must be provided"))
       ((unless (implies fix pred))
        (er hard? 'def-1d-arr
            "If :fix is supplied, :pred must also be"))
       (xdoc::mksym-package-symbol (or pkg-sym arrname slotname))
       (arrname (or arrname (xdoc::mksym slotname 'arr)))
       (slotname (or slotname (xdoc::mksym arrname 'val)))
       (type-decl (or type-decl `(satisfies ,pred)))
       (features (cond ((and pred fix) '(:pred :fix))
                       (pred '(:pred))))
       (symsubst `((_arrname_ . ,arrname)
                   (_slotname_ . ,slotname)
                   (_fix_ . ,fix)
                   (_pred_ . ,pred)
                   (_type-decl_ . ,type-decl)
                   (_default-val_ . ,default-val)))
       (strsubst (tmpl-symbol-alist-to-str-alist symsubst))
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






(local
 (progn

   (encapsulate nil
     (defund widgp (x)
       (declare (xargs :guard t))
       (eq x 'the-default-widg))

     (defund widg-fix (x)
       (declare (Xargs :guard t))
       (if (widgp x)
           x
         'the-default-widg))

     (local (in-theory (enable widg-fix)))

     (defthm widgp-of-widg-fix
       (widgp (widg-fix x)))

     (defthm widg-fix-when-widgp
       (implies (widgp x)
                (equal (widg-fix x) x))))


   ;; test
   (def-1d-arr :arrname widgarr
     :slotname widg
     :pred widgp
     :fix widg-fix
     :type-decl (satisfies widgp)
     :default-val the-default-widg)

   (encapsulate nil
     (defund swidgp (x)
       (declare (xargs :guard t))
       (symbolp x))

     (defund swidg-fix (x)
       (declare (Xargs :guard t))
       (if (swidgp x)
           x
         'the-default-swidg))

     (local (in-theory (enable swidg-fix)))

     ;; (defthm swidgp-of-swidg-fix
     ;;   (swidgp (swidg-fix x)))

     (defthm swidg-fix-when-swidgp
       (implies (swidgp x)
                (equal (swidg-fix x) x))))


   ;; test
   (def-1d-arr :arrname swidgarr
     :slotname swidg
     :pred swidgp
     :fix swidg-fix
     :type-decl (and symbol (satisfies swidgp))
     :pkg-sym xdoc::asdfs
     :default-val the-default-swidg)

   ;; default-val is not value to which we fix
   (def-1d-arr :arrname swidgarr2
     :slotname swidg2
     :pred swidgp
     :fix swidg-fix
     :type-decl (and symbol (satisfies swidgp))
     :pkg-sym xdoc::asdfs
     :default-val the-default-swidg2)

   (def-1d-arr :arrname objarr
     :slotname obj
     :default-val asdfa)

   (def-1d-arr :arrname swidgarr3
     :slotname swidg3
     :pred swidgp
     :type-decl (and symbol (satisfies swidgp))
     :pkg-sym xdoc::asdfs
     :default-val the-default-swidg2)))





#||


(def-universal-equiv widg-equiv
  :equiv-terms ((equal (widg-fix x))))


(def-universal-equiv widgs-equiv
  :qvars (i)
  :equiv-terms ((widg-equiv (nth i x))))

(defcong widgs-equiv widg-equiv (nth i x) 2
  :hints(("Goal" :in-theory (e/d (widgs-equiv-necc)
                                 (widg-equiv)))))

(defcong widgs-equiv widgs-equiv (update-nth i v x) 3
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defcong widg-equiv widgs-equiv (update-nth i v x) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))


(defstobj widgarr$c
  (widgs$c :type (array (satisfies widgp) (0))
           :initially the-default-widg
           :resizable t)
  :inline t)


(defthm widgp-nth-of-widgs$cp
  (implies (and (widgs$cp x)
                (< (nfix n) (len x)))
           (widgp (nth n x))))

(defthm widgs$cp-of-update-nth
  (implies (and (widgs$cp x)
                (widgp v)
                (<= (nfix n) (len x)))
           (widgs$cp (update-nth n v x))))

(defthm widgs$cp-of-resize-list
  (implies (and (widgs$cp x)
                (widgp default))
           (widgs$cp (resize-list x n default))))

(defun widgarr$ap (widgarr$a)
  (declare (xargs :guard t)
           (ignorable widgarr$a))
  t)

(defun create-widgarr$a ()
  (declare (xargs :guard t))
  nil)

(defun widgs$a-length (widgarr$a)
  (declare (xargs :guard (widgarr$ap widgarr$a)
                  :verify-guards t))
  (len widgarr$a))

(defun resize-widgs$a (i widgarr$a)
  (declare (xargs :guard (widgarr$ap widgarr$a)))
  (resize-list widgarr$a i 'the-default-widg))

(defun widgs$ai (i widgarr$a)
  (declare (xargs :guard (and (widgarr$ap widgarr$a)
                              (integerp i)
                              (<= 0 i)
                              (< i (widgs$a-length widgarr$a)))
                  :verify-guards t))
  (widg-fix (ec-call (nth i widgarr$a))))

(defun update-widgs$ai (i v widgarr$a)
  (declare (xargs :guard (and (widgarr$ap widgarr$a)
                              (integerp i)
                              (<= 0 i)
                              (< i (widgs$a-length widgarr$a))
                              (widgp v))
                  :verify-guards t))
  (ec-call (update-nth i (widg-fix v) widgarr$a)))

(defun-nx widgarr$corr (widgarr$c widgarr$a)
  (and (widgarr$cp widgarr$c)
       (equal (len widgarr$a) (len (nth 0 widgarr$c)))
       (widgs-equiv widgarr$a (nth 0 widgarr$c))))

(local (in-theory (disable nth resize-list
                           (widgarr$corr))))

(local (set-default-hints
        '((and stable-under-simplificationp
               (let ((lit (car (last clause))))
                 (and (consp lit)
                      (eq (car lit) 'widgs-equiv)
                      `(:expand (,lit))))))))

(local (defthm nths-equal-by-widgs-equiv
         (implies (and (widgs-equiv x y)
                       (widgs$cp x)
                       (< (nfix i) (len x)))
                  (equal (equal (nth i x) (widg-fix (nth i y)))
                         t))
         :hints (("goal" :use widgs-equiv-necc
                  :in-theory (e/d (widg-equiv)
                                  (widgs-equiv-necc
                                   widgs-equiv-implies-widg-equiv-nth-2))
                  :do-not-induct t))))

(local (in-theory (enable nth-of-resize-list-split)))

(defabsstobj-events widgarr
  :exports ((widgs-length :exec widgs$c-length :logic widgs$a-length)
            (get-widg :exec widgs$ci :logic widgs$ai)
            (set-widg :exec update-widgs$ci :logic update-widgs$ai)
            resize-widgs))
||#
