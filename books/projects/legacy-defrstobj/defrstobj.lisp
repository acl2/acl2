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

; (depends-on "build/defrec-certdeps/DEFSTOBJ-FIELD-TEMPLATE.certdep" :dir :system)
; (depends-on "build/defrec-certdeps/DEFSTOBJ-TEMPLATE.certdep" :dir :system)

(in-package "RSTOBJ")
(include-book "def-typed-record")
(include-book "g-delete-keys")
(include-book "fancy-worseguy")
(include-book "misc/definline" :dir :system)
(include-book "misc/records" :dir :system)
(include-book "std/util/bstar" :dir :system)

#||
;; fool dependency scanner into including the array lemmas book, since our
;; defrstobj event will include it.
(include-book "array-lemmas")
||#


(defun-nx non-executable-nth (n x)
  ;; Used in good-stp below, to get around stobj restrictions
  (nth n x))


; The DEFRSTOBJ macro.
;
; Example:
;
;    (defrstobj st
;
;      (regs :type (array (unsigned-byte 64) (32))
;            :initially 0
;            :typed-record u32-tr-p)
;
;      (pc   :type (unsigned-byte 64)
;            :initially 0)
;
;      (mem  :type (array (unsigned-byte 8) (*mem-size*))
;            :initially 0
;            :typed-record u8-tr-p)
;
;      :inline t)
;
; The syntax of DEFRSTOBJ is basically that of DEFSTOBJ, except that each array
; field needs to have a :TYPED-RECORD argument that names the recognizer
; function for a typed record that was introduced by DEF-TYPED-RECORD.  See the
; file defrstobj-tests.lisp for several more examples, including examples of
; how to use DEF-TYPED-RECORD.
;
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
          (remove-keyword :typed-record (cdr rsf)))))

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

(defun make-fta (field-name defstobj-fld-template tr-alist mksym-pkg)

  (b* (((list recog-name type init accessor-name updater-name length-name
              resize-name resizable other)
        ;; BOZO this has to be kept in sync with defstobj-field-template
        (destructure-defstobj-field-template defstobj-fld-template))

; For array fields, we'll add an :arr-rec-name field that gives the name of the
; additional record part of the array+record pair we'll use to implement this
; array.

       (typed-record (cdr (assoc field-name tr-alist)))

       (arr-rec-name
        (and length-name (mksym field-name '-RSTOBJ-REC)))

       (- (or (and length-name
                   typed-record)
              (and (not length-name)
                   (not typed-record))
              (er hard? 'make-fta
                  "Field ~x0 is not allowed; each array needs to have a ~
                   :typed-record entry, and non-arrays may not have ~
                   :typed-record entries." field-name))))

    `((:field-name    . ,field-name)
      (:recog-name    . ,recog-name)
      (:type          . ,type)
      (:init          . ,init)
      (:accessor-name . ,accessor-name)
      (:updater-name  . ,updater-name)
      (:length-name   . ,length-name)
      (:resize-name   . ,resize-name)
      (:resizable     . ,resizable)
      (:other         . ,other)
      (:offset        . ,(acl2::defconst-name accessor-name))
      (:arr-rec-name  . ,arr-rec-name)
      (:typed-record  . ,typed-record))))

(defun make-ftas (field-names st-fld-templates tr-alist mksym-pkg)
  (if (atom field-names)
      nil
    (cons (make-fta (car field-names) (car st-fld-templates) tr-alist mksym-pkg)
          (make-ftas (cdr field-names) (cdr st-fld-templates) tr-alist mksym-pkg))))

(defun make-arr-rec-fields (ftas)
  ;; Build the "record" entries for the array/record pairs
  (b* (((when (atom ftas))
        nil)
       (name (cdr (assoc :arr-rec-name (car ftas))))
       ((unless name)
        (make-arr-rec-fields (cdr ftas))))
    (cons `(,name :initially nil)
          (make-arr-rec-fields (cdr ftas)))))

(defun find-fta (name ftas)
  (cond ((atom ftas)
         nil)
        ((equal (cdr (assoc :field-name (car ftas))) name)
         (car ftas))
        (t
         (find-fta name (cdr ftas)))))

(defun collect-array-ftas (ftas)
  (if (atom ftas)
      nil
    (if (cdr (assoc :length-name (car ftas)))
        (cons (car ftas) (collect-array-ftas (cdr ftas)))
      (collect-array-ftas (cdr ftas)))))

(defun fta-field-names (ftas)
  (if (atom ftas)
      nil
    (cons (cdr (assoc :field-name (car ftas)))
          (fta-field-names (cdr ftas)))))



(defun fta-fns (fta)
  (remove nil (list (cdr (assoc :recog-name fta))
                    (cdr (assoc :accessor-name fta))
                    (cdr (assoc :updater-name fta))
                    (cdr (assoc :length-name fta))
                    (cdr (assoc :resize-name fta)))))

(defun fta-list-fns (ftas)
  (if (atom ftas)
      nil
    (append (fta-fns (car ftas))
            (fta-list-fns (cdr ftas)))))

(defun type-prescriptions-from-names (names)
  (if (atom names)
      nil
    (cons `(:type-prescription ,(car names))
          (type-prescriptions-from-names (cdr names)))))

(defun executable-counterparts-from-names (names)
  (if (atom names)
      nil
    (cons `(:executable-counterpart ,(car names))
          (executable-counterparts-from-names (cdr names)))))



(defun typed-record-fi-pairs (fn wrld)
  (b* ((look (assoc fn (table-alist 'typed-records wrld)))
       ((unless look)
        (er hard? 'typed-record-fi-pairs
            "~x0 does not look like a valid typed-record recognizer.  The ~
             current typed-record recognizers are ~&1."
            fn
            (strip-cars (table-alist 'typed-records wrld)))))
    (cdr (assoc :fi-pairs (cdr look)))))

(defun typed-record-thms (fn wrld)
  (b* ((look (assoc fn (table-alist 'typed-records wrld)))
       ((unless look)
        (er hard? 'typed-record-thms
            "~x0 does not look like a valid typed-record recognizer.  The ~
             current typed-record recognizers are ~&1."
            fn
            (strip-cars (table-alist 'typed-records wrld)))))
    (cdr (assoc :theorems (cdr look)))))

(defun collect-typed-record-thms (ftas wrld)
  (b* (((when (atom ftas))
        nil)
       (length-name (cdr (assoc :length-name (car ftas))))
       ((unless length-name)
        ;; Not an array, nothing to do
        (collect-typed-record-thms (cdr ftas) wrld))
       (typed-record     (cdr (assoc :typed-record (car ftas)))))
    (append (typed-record-thms typed-record wrld)
            (collect-typed-record-thms (cdr ftas) wrld))))







(defun array-boilerplate (ftas mksym-pkg wrld)
  ;; Basic theorems about the well-formed list recognizer for an array field.
  (b* (((when (atom ftas))
        nil)
       (length-name (cdr (assoc :length-name (car ftas))))
       ((unless length-name)
        ;; not an array, nothing to do.
        (array-boilerplate (cdr ftas) mksym-pkg wrld))

       (typed-record       (cdr (assoc :typed-record (car ftas))))
       (fi-pairs           (typed-record-fi-pairs typed-record wrld))
       (elem-list-p-lambda (second (assoc 'elem-list-p fi-pairs)))
       (elem-list-p        (third elem-list-p-lambda))

       (recog-name    (cdr (assoc :recog-name (car ftas))))
       (full-type     (cdr (assoc :type (car ftas)))) ;; with the array part
       (elem-type     (second full-type))             ;; just the element part
       (elem-p-of-val (translate-declaration-to-guard elem-type 'val wrld)))

    (append
     `((defthm ,(mksym recog-name '-of-make-list-ac)
         (implies (and ,elem-p-of-val
                       (,recog-name acc))
                  (,recog-name (make-list-ac n val acc)))
         :hints(("Goal" :in-theory (enable make-list-ac))))

       (defthm ,(mksym 'true-listp-when- recog-name)
         (implies (,recog-name x)
                  (true-listp x))
         :rule-classes :compound-recognizer)

       (defthm ,(mksym 'elem-list-p-for- typed-record '-when- recog-name)
         (implies (,recog-name x)
                  ,elem-list-p)))

     (array-boilerplate (cdr ftas) mksym-pkg wrld))))


(defun weak-stp-conjuncts (stobj-name ftas wrld)
  ;; The array-rec-pair-p requirement for each array array/record pair.
  (b* (((when (atom ftas))
        nil)
       (length-name (cdr (assoc :length-name (car ftas))))
       ((unless length-name)
        ;; Not an array, nothing to do
        (weak-stp-conjuncts stobj-name (cdr ftas) wrld))

       (offset           (cdr (assoc :offset (car ftas))))
       (arr-rec-name     (cdr (assoc :arr-rec-name (car ftas))))
       (typed-record     (cdr (assoc :typed-record (car ftas))))

       ;; Now, we need to look up the proper array-rec-pair-p function
       ;; in the world.
       (fi-pairs         (typed-record-fi-pairs typed-record wrld))
       (array-rec-pair-p (second (assoc 'array-rec-pair-p fi-pairs))))

    (cons `(,array-rec-pair-p (nth ,offset ,stobj-name)
                              (,arr-rec-name ,stobj-name)
                              (,length-name ,stobj-name))
          (weak-stp-conjuncts stobj-name (cdr ftas) wrld))))

(defun good-stp-conjuncts (stobj-name ftas wrld)
  (b* (((when (atom ftas))
        nil)
       (length-name       (cdr (assoc :length-name (car ftas))))
       ((unless length-name)
        ;; Not an array, nothing to do
        (good-stp-conjuncts stobj-name (cdr ftas) wrld))

       (arr-rec-name      (cdr (assoc :arr-rec-name (car ftas))))
       (typed-record      (cdr (assoc :typed-record (car ftas))))
       (offset            (cdr (assoc :offset (car ftas))))
       (fi-pairs          (typed-record-fi-pairs typed-record wrld))
       (tr-delete-indices (second (assoc 'tr-delete-indices fi-pairs)))
       (array-rec-pair-p  (second (assoc 'array-rec-pair-p fi-pairs))))
    (cons `(mbe :logic (,array-rec-pair-p
                        (non-executable-nth ,offset ,stobj-name)
                        (,arr-rec-name ,stobj-name)
                        (,length-name ,stobj-name))
                :exec
                (or
                 ;; This part should get executed:
                 (not (,arr-rec-name ,stobj-name))
                 ;; This part shouldn't get executed:
                 (equal (,arr-rec-name ,stobj-name)
                        (,tr-delete-indices (,length-name ,stobj-name)
                                            (,arr-rec-name ,stobj-name)))))
          (good-stp-conjuncts stobj-name (cdr ftas) wrld))))

(defun collect-array-rec-pair-ps (ftas wrld)
  (b* (((when (atom ftas))
        nil)
       (length-name (cdr (assoc :length-name (car ftas))))
       ((unless length-name)
        ;; Not an array, nothing to do
        (collect-array-rec-pair-ps (cdr ftas) wrld))

       (typed-record     (cdr (assoc :typed-record (car ftas))))
       (fi-pairs         (typed-record-fi-pairs typed-record wrld))
       (array-rec-pair-p (second (assoc 'array-rec-pair-p fi-pairs))))

    (cons array-rec-pair-p
          (collect-array-rec-pair-ps (cdr ftas) wrld))))



(defun array-update-wrapper (stobj-name fta mksym-pkg wrld)
  (b* ((field-name          (cdr (assoc :field-name fta)))
       (offset              (cdr (assoc :offset fta)))
       (length-name         (cdr (assoc :length-name fta)))
       (updater-name        (cdr (assoc :updater-name fta)))

       ;; bozo update-arr-rec-name probably has the wrong package,
       ;; and arr-rec-offset is horrible.  do this better.
       (arr-rec-name        (cdr (assoc :arr-rec-name fta)))
       (update-arr-rec-name (mksym 'update- arr-rec-name))
       (arr-rec-offset      (acl2::defconst-name arr-rec-name))

       (type                (cdr (assoc :type fta))) ;; full array type
       (etype               (second type))
       (etype-of-val        (translate-declaration-to-guard etype 'val wrld))
       (weak-stp            (mksym 'weak- stobj-name '-p))

       (typed-record      (cdr (assoc :typed-record fta)))
       (fi-pairs          (typed-record-fi-pairs typed-record wrld))
       (tr-set            (second (assoc 'tr-set fi-pairs)))
       (array-to-tr       (second (assoc 'array-to-tr fi-pairs)))
       (tr-to-array       (second (assoc 'tr-to-array fi-pairs)))
       (tr-delete-indices (second (assoc 'tr-delete-indices fi-pairs)))

       (getter      (mksym field-name '-getter))
       (setter      (mksym field-name '-setter)))

    `(progn

       (defund-nx ,getter (,stobj-name)
         (,array-to-tr (,length-name ,stobj-name)
                       (nth ,offset ,stobj-name)
                       (,arr-rec-name ,stobj-name)))

       (defund-nx ,setter (val ,stobj-name)
         (let* ((arr (nth ,offset ,stobj-name))
                (len (,length-name ,stobj-name))
                (arr (,tr-to-array len val arr))
                (rec (,tr-delete-indices len val))
                (,stobj-name  (update-nth ,offset arr ,stobj-name))
                (,stobj-name  (,update-arr-rec-name rec ,stobj-name)))
           ,stobj-name))

       (local
        (encapsulate
          ()
          (local (in-theory (enable ,getter ,setter)))

          (defthm ,(mksym weak-stp '-of- setter)
            (implies (,weak-stp ,stobj-name)
                     (,weak-stp (,setter val ,stobj-name))))

          (defthm ,(mksym getter '-of- setter)
            (equal (,getter (,setter val ,stobj-name))
                   val))

          (defthm ,(mksym setter '-of- getter)
            (implies (,weak-stp ,stobj-name)
                     (equal (,setter (,getter ,stobj-name) ,stobj-name)
                            ,stobj-name)))

          (defthm ,(mksym setter '-of- setter)
            (implies (,weak-stp ,stobj-name)
                     (equal (,setter val1 (,setter val2 ,stobj-name))
                            (,setter val1 ,stobj-name))))

          (defthm ,(mksym getter '-after-updating-other)
            (implies (and (,weak-stp ,stobj-name)
                          (natp n)
                          (not (equal n ,offset))
                          (not (equal n ,arr-rec-offset)))
                     (equal (,getter (update-nth n val ,stobj-name))
                            (,getter ,stobj-name))))

          (defthm ,(mksym setter '-after-updating-other)
            (implies (and (,weak-stp ,stobj-name)
                          (natp n)
                          (not (equal n ,offset))
                          (not (equal n ,arr-rec-offset)))
                     (equal (,setter val1 (update-nth n val2 ,stobj-name))
                            (update-nth n val2 (,setter val1 ,stobj-name)))))

          (defthm ,(mksym 'other-after- setter)
            (implies (and (,weak-stp ,stobj-name)
                          (natp n)
                          (not (equal n ,offset))
                          (not (equal n ,arr-rec-offset)))
                     (equal (nth n (,setter val ,stobj-name))
                            (nth n ,stobj-name))))

          (defthm ,(mksym updater-name '-when-good-inputs)
            (implies (and (,weak-stp ,stobj-name)
                          (natp i)
                          ,etype-of-val
                          (< i (,length-name ,stobj-name)))
                     (equal (,updater-name i val ,stobj-name)
                            (,setter (,tr-set i val (,getter ,stobj-name)) ,stobj-name))))

          )))))

(defun array-update-wrappers (stobj-name ftas mksym-pkg wrld)
  (b* (((when (atom ftas))
        nil)
       (length-name (cdr (assoc :length-name (car ftas))))
       ((unless length-name)
        ;; Not an array, nothign to do for this field
        (array-update-wrappers stobj-name (cdr ftas) mksym-pkg wrld)))
    (cons (array-update-wrapper stobj-name (car ftas) mksym-pkg wrld)
          (array-update-wrappers stobj-name (cdr ftas) mksym-pkg wrld))))



(defun make-noninterference-theorems1 (stobj-name field1 other-fields mksym-pkg)
  (b* (((when (atom other-fields))
        nil)
       ((when (equal field1 (car other-fields)))
        (make-noninterference-theorems1 stobj-name field1 (cdr other-fields) mksym-pkg))
       (field2        (car other-fields))
       (field1-getter (mksym field1 '-getter))
       (field1-setter (mksym field1 '-setter))
       (field2-setter (mksym field2 '-setter))
       (weak-stp      (mksym 'weak- stobj-name '-p))
       (thms
        `((defthm ,(mksym field1-getter '-of- field2-setter)
            (implies (,weak-stp ,stobj-name)
                     (equal (,field1-getter (,field2-setter val ,stobj-name))
                            (,field1-getter ,stobj-name)))
            :hints(("Goal" :in-theory (enable ,field1-getter
                                              ,field2-setter))))
          (defthm ,(mksym field1-setter '-of- field2-setter)
            (implies (and (,weak-stp ,stobj-name)
                          (syntaxp (symbol< ',field1 ',field2))
                          )
                     (equal (,field1-setter val1 (,field2-setter val2 ,stobj-name))
                            (,field2-setter val2 (,field1-setter val1 ,stobj-name))))
            :hints(("Goal" :in-theory (enable ,field1-setter ,field2-setter)))))))
    (append thms
            (make-noninterference-theorems1 stobj-name field1 (cdr other-fields) mksym-pkg))))

(defun make-noninterference-theorems (stobj-name fieldnames all-fieldnames mksym-pkg)
  (if (atom fieldnames)
      nil
    (append
     (make-noninterference-theorems1 stobj-name (car fieldnames) all-fieldnames mksym-pkg)
     (make-noninterference-theorems stobj-name (cdr fieldnames) all-fieldnames mksym-pkg))))

(defun make-noninterference-top (stobj-name ftas mksym-pkg)
  (let* ((array-ftas (collect-array-ftas ftas))
         (all-fieldnames (fta-field-names array-ftas)))
    `(progn
       ,@(make-noninterference-theorems stobj-name all-fieldnames all-fieldnames mksym-pkg))))




(defun make-cond-pairs-for-get1 (stobj-name ftas misc-fta mksym-pkg)

  (b* (((when (atom ftas))
        ;; Default case: get the key out of the extra MISC field.
        (b* ((get-misc (cdr (assoc :accessor-name misc-fta))))
          (list `(t (g name (,get-misc ,stobj-name))))))

       (field-name    (cdr (assoc :field-name (car ftas))))
       (keyword       (intern-in-package-of-symbol (symbol-name field-name) :keyword))
       (length-name   (cdr (assoc :length-name (car ftas))))
       (accessor-name (cdr (assoc :accessor-name (car ftas))))

       ((unless length-name)
        ;; Ordinary field, use the getter for this field
        (cons `((equal name ,keyword)
                (,accessor-name ,stobj-name))
              (make-cond-pairs-for-get1 stobj-name (cdr ftas) misc-fta mksym-pkg)))

       ;; Array field, use the special accessor
       (getter (mksym field-name '-getter)))
    (cons `((equal name ,keyword)
            (,getter ,stobj-name))
          (make-cond-pairs-for-get1 stobj-name (cdr ftas) misc-fta mksym-pkg))))


(defun make-cond-pairs-for-set1 (stobj-name ftas misc-fta mksym-pkg)

  (b* (((when (atom ftas))
        ;; Default case: set the key out of the extra MISC field.
        (b* ((get-misc (cdr (assoc :accessor-name misc-fta)))
             (set-misc (cdr (assoc :updater-name misc-fta))))
          (list `(t (,set-misc (s name val (,get-misc ,stobj-name)) ,stobj-name)))))

       (field-name    (cdr (assoc :field-name (car ftas))))
       (keyword       (intern-in-package-of-symbol (symbol-name field-name) :keyword))
       (length-name   (cdr (assoc :length-name (car ftas))))
       (updater-name  (cdr (assoc :updater-name (car ftas))))

       ((unless length-name)
        ;; Ordinary field, use the setter for this field
        (cons `((equal name ,keyword)
                (,updater-name val ,stobj-name))
              (make-cond-pairs-for-set1 stobj-name (cdr ftas) misc-fta mksym-pkg)))

       ;; Array field, use the special updater
       (setter (mksym field-name '-setter)))
    (cons `((equal name ,keyword)
            (,setter val ,stobj-name))
          (make-cond-pairs-for-set1 stobj-name (cdr ftas) misc-fta mksym-pkg))))


(defun make-st-wrappers (stobj-name ftas misc-fta mksym-pkg
                                    st-good update-st-good
                                    st-badplace update-st-badplace)
  (b* ((get1          (mksym stobj-name '-get1))
       (set1          (mksym stobj-name '-set1))
       (weak-stp      (mksym 'weak- stobj-name '-p))
       (good-stp      (mksym 'good- stobj-name '-p)))

    `(progn

       (defund-nx ,get1 (name ,stobj-name)
         (cond ((equal name :rstobj-good)
                (,st-good ,stobj-name))
               ((equal name :rstobj-badplace)
                (,st-badplace ,stobj-name))
               ,@(make-cond-pairs-for-get1 stobj-name ftas misc-fta mksym-pkg)))

       (defund-nx ,set1 (name val ,stobj-name)
         (cond ((equal name :rstobj-good)
                (,update-st-good val ,stobj-name))
               ((equal name :rstobj-badplace)
                (,update-st-badplace val ,stobj-name))
               ,@(make-cond-pairs-for-set1 stobj-name ftas misc-fta mksym-pkg)))

       (local
        (encapsulate
          ()
          (local (in-theory (enable ,get1 ,set1)))

          (defthm ,(mksym weak-stp '-of- set1)
            (implies (,weak-stp ,stobj-name)
                     (,weak-stp (,set1 name val ,stobj-name)))
            :hints(("Goal" :in-theory (enable member-equal))))

          (defthm ,(mksym good-stp '-of- set1)
            (implies (and (,good-stp ,stobj-name)
                          (force (not (equal name :rstobj-good))))
                     (,good-stp (,set1 name val ,stobj-name)))
            :hints(("Goal" :in-theory (enable ,good-stp member-equal))))

          (defthm ,(mksym get1 '-of- set1 '-same)
            (equal (,get1 name (,set1 name val ,stobj-name))
                   val))

          (defthm ,(mksym get1 '-of- set1 '-diff)
            (implies (and (,weak-stp ,stobj-name)
                          (not (equal name1 name2)))
                     (equal (,get1 name1 (,set1 name2 val ,stobj-name))
                            (,get1 name1 ,stobj-name))))

          (defthm ,(mksym set1 '-of- get1 '-same)
            (implies (,weak-stp ,stobj-name)
                     (equal (,set1 name (,get1 name ,stobj-name) ,stobj-name)
                            ,stobj-name)))

          (defthm ,(mksym set1 '-of- set1 '-same)
            (implies (,weak-stp ,stobj-name)
                     (equal (,set1 name val1 (,set1 name val2 ,stobj-name))
                            (,set1 name val1 ,stobj-name))))

          (defthm ,(mksym set1 '-of- set1 '-diff)
            (implies (and (not (equal name1 name2))
                          (,weak-stp ,stobj-name))
                     (equal (,set1 name1 val1 (,set1 name2 val2 ,stobj-name))
                            (,set1 name2 val2 (,set1 name1 val1 ,stobj-name))))))))))



(defun make-exec-getter (stobj-name fta mksym-pkg wrld)
  (b* ((fieldname     (cdr (assoc :field-name fta)))
       (length-name   (cdr (assoc :length-name fta)))
       (accessor-name (cdr (assoc :accessor-name fta)))
       (keyword       (intern-in-package-of-symbol (symbol-name fieldname) :keyword))

       (good-stp      (mksym 'GOOD- stobj-name '-P))
       (st-get        (mksym stobj-name '-GET))

       ((unless length-name)
        ;; Normal field, not an array
        `(definline ,(mksym 'get- fieldname) (,stobj-name)
           (declare (xargs :stobjs ,stobj-name
                           :guard (,good-stp ,stobj-name)))
           (mbe :logic (,st-get ,keyword ,stobj-name)
                :exec (,accessor-name ,stobj-name))))

       (typed-record (cdr (assoc :typed-record fta)))
       (fi-pairs     (typed-record-fi-pairs typed-record wrld))
       (tr-get       (second (assoc 'tr-get fi-pairs)))
       (getter       (mksym fieldname '-getter)))

    `(definline ,(mksym 'get- fieldname) (i ,stobj-name)
       (declare (xargs :stobjs ,stobj-name
                       :guard (and (,good-stp ,stobj-name)
                                   (natp i)
                                   (< i (,length-name ,stobj-name)))
                       :guard-hints(("Goal" :in-theory (enable ,getter)))))
       (mbe :logic (,tr-get i (,st-get ,keyword ,stobj-name))
            :exec (,accessor-name i ,stobj-name)))))

(defun make-exec-getters (stobj-name ftas mksym-pkg wrld)
  (if (atom ftas)
      nil
    (cons (make-exec-getter stobj-name (car ftas) mksym-pkg wrld)
          (make-exec-getters stobj-name (cdr ftas) mksym-pkg wrld))))


(defun make-exec-setter (stobj-name fta mksym-pkg wrld)
  (b* ((fieldname     (cdr (assoc :field-name fta)))
       (length-name   (cdr (assoc :length-name fta)))
       (updater-name  (cdr (assoc :updater-name fta)))
       (type          (cdr (assoc :type fta)))
       (keyword       (intern-in-package-of-symbol (symbol-name fieldname) :keyword))

       (good-stp      (mksym 'GOOD- stobj-name '-P))
       (st-get        (mksym stobj-name '-GET))
       (st-set        (mksym stobj-name '-SET))

       ((unless length-name)
        ;; Normal field, not an array
        `(definline ,(mksym 'set- fieldname) (x ,stobj-name)
           (declare (xargs :stobjs ,stobj-name
                           :guard (and (,good-stp ,stobj-name)
                                       ,(translate-declaration-to-guard type 'x wrld))))
           (mbe :logic (,st-set ,keyword x ,stobj-name)
                :exec (,updater-name x ,stobj-name))))

       (etype        (second type))
       (typed-record (cdr (assoc :typed-record fta)))
       (fi-pairs     (typed-record-fi-pairs typed-record wrld))
       (tr-set       (second (assoc 'tr-set fi-pairs))))

    `(definline ,(mksym 'set- fieldname) (i x ,stobj-name)
       (declare (xargs :stobjs ,stobj-name
                       :guard (and (,good-stp ,stobj-name)
                                   (natp i)
                                   (< i (,length-name ,stobj-name))
                                   ,(translate-declaration-to-guard etype 'x wrld))
                       :guard-hints(("Goal" :in-theory (disable ,updater-name)))))
       (mbe :logic (,st-set ,keyword
                            (,tr-set i x (,st-get ,keyword ,stobj-name))
                            ,stobj-name)
            :exec (,updater-name i x ,stobj-name)))))


(defun make-exec-setters (stobj-name ftas mksym-pkg wrld)
  (if (atom ftas)
      nil
    (cons (make-exec-setter stobj-name (car ftas) mksym-pkg wrld)
          (make-exec-setters stobj-name (cdr ftas) mksym-pkg wrld))))


(defun field-keywords (ftas)
  (if (atom ftas)
      nil
    (b* ((field-name    (cdr (assoc :field-name (car ftas))))
         (keyword       (intern-in-package-of-symbol (symbol-name field-name) :keyword)))
      (cons keyword
            (field-keywords (cdr ftas))))))


(defun make-cond-pairs-for-badguy1 (get1 keywords)
  ;; Doesn't introduce the final T pair
  (b* (((when (atom keywords))
        nil)
       (kwd1 (car keywords))
       (pair1 `((not (equal (,get1 ,kwd1 x)
                            (,get1 ,kwd1 y)))
                (list :mismatch ,kwd1))))
    (cons pair1
          (make-cond-pairs-for-badguy1 get1 (cdr keywords)))))



(defun badguy-finds-diffs-lemma (stobj-name badguy1 fta)
  ;; For a non-array field
  (b* ((mksym-pkg stobj-name)
       (field-name    (cdr (assoc :field-name fta)))
       (accessor-name (cdr (assoc :accessor-name fta))))

    `(local (defthm ,(mksym badguy1 '-finds-diffs-in- field-name)
              (implies (not (equal (,accessor-name x)
                                   (,accessor-name y)))
                       (,badguy1 x y))))))

(defun badguy-finds-diffs-lemma-arr (stobj-name badguy1 weak-stp fta wrld)
  (b* ((mksym-pkg stobj-name)
       (field-name    (cdr (assoc :field-name fta)))
       (offset        (cdr (assoc :offset fta)))
       (arr-rec-name  (cdr (assoc :arr-rec-name fta)))
       (length-name   (cdr (assoc :length-name fta)))
       (typed-record  (cdr (assoc :typed-record fta)))
       (fi-pairs      (typed-record-fi-pairs typed-record wrld))
       (array-to-tr   (second (assoc 'array-to-tr fi-pairs)))
       (pair-p        (second (assoc 'array-rec-pair-p fi-pairs)))
       (tr-thm        (let ((mksym-pkg array-to-tr))
                        (mksym 'equal-of- array-to-tr)))
       (getter        (mksym field-name '-getter)))
    `(local (defthm ,(mksym badguy1 '-finds-diffs-in- field-name)
              (implies (and (,weak-stp x)
                            (,weak-stp y)
                            (or (not (equal (nth ,offset x)
                                            (nth ,offset y)))
                                (not (equal (,arr-rec-name x)
                                            (,arr-rec-name y)))))
                       (,badguy1 x y))
              :hints(("Goal"
                      :in-theory (e/d (,weak-stp ,getter ,length-name ,tr-thm)
                                      (,pair-p))))))))

(defun badguy-finds-diffs-lemmas (stobj-name badguy1 weak-stp ftas wrld)
  (if (atom ftas)
      nil
    (cons
     (if (cdr (assoc :length-name (car ftas)))
         (badguy-finds-diffs-lemma-arr stobj-name badguy1 weak-stp (car ftas) wrld)
       (badguy-finds-diffs-lemma stobj-name badguy1 (car ftas)))
     (badguy-finds-diffs-lemmas stobj-name badguy1 weak-stp (cdr ftas) wrld))))


(defund equal-when-weak-stp-rhs (ftas)
  ;; Makes a list of conjuncts for these fields
  (if (atom ftas)
      nil
    (b* ((fta           (car ftas))
         (accessor-name (cdr (assoc :accessor-name fta)))
         (offset        (cdr (assoc :offset fta)))
         (arr-rec-name  (cdr (assoc :arr-rec-name fta)))
         (length-name   (cdr (assoc :length-name fta))))
      (cons
       (if length-name
           `(and (equal (nth ,offset x) (nth ,offset y))
                 (equal (,arr-rec-name x) (,arr-rec-name y)))
         `(equal (,accessor-name x) (,accessor-name y)))
       (equal-when-weak-stp-rhs (cdr ftas))))))


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

(defun defrstobj-fn (name args wrld)
  (declare (ignorable wrld)
           (xargs :mode :program))
  (b* ((mksym-pkg     name)

       ((mv erp rsfs st-kw-alist)
        (partition-rest-and-keyword-args args *defstobj-keywords*))
       (- (or (not erp)
              (er hard? 'defrstobj-fn "Invalid DEFRSTOBJ syntax for ~x0." name)))
       (- (or (consp rsfs)
              (er hard? 'defrstobj-fn "Expected at least one field for ~x0." name)))

       (tr-alist      (tr-alist rsfs))
       (st-fields     (eat-typed-records rsfs))
       (st-kw-part    (alist-to-keyword-alist st-kw-alist nil))
       (st-template   (defstobj-template name (append st-fields st-kw-part) wrld))
       ((list namep create-name st-fld-templates
; Matt K. mod: :doc is no longer supported for defthm after v7-1
              ;; ?doc
              ?inline ?congruent-to
              ?non-memoizable)
        ;; BOZO this has to be kept in sync with defstobj-template.
        (destructure-defstobj-template st-template))

       (ftas (make-ftas (strip-cars tr-alist) st-fld-templates tr-alist mksym-pkg))

       (set           (mksym name '-SET))
       (get           (mksym name '-GET))
       (set1          (mksym name '-SET1))
       (get1          (mksym name '-GET1))
       (weak-stp      (mksym 'WEAK- name '-P))
       (good-stp      (mksym 'GOOD- name '-P))
       (bad-stp       (mksym 'BAD- name '-P))
       (to            (mksym 'TO- name '-RSTOBJ))
       (from          (mksym 'FROM- name '-RSTOBJ))
       (misc-name     (mksym name '-RSTOBJ-MISC))
       (good-name     (mksym name '-RSTOBJ-GOOD))
       (badplace-name (mksym name '-RSTOBJ-BADPLACE))
       (user-keys     (field-keywords ftas))
       (- (or (not (member :rstobj-good user-keys))
              (er hard? 'defrstobj-fn "The field name RSTOBJ-GOOD is reserved.")))
       (- (or (not (member :rstobj-badplace user-keys))
              (er hard? 'defrstobj-fn "The field name RSTOBJ-BADPLACE is reserved.")))
       (user-keys     (list* :rstobj-good :rstobj-badplace user-keys))

       (st-fields+    (append st-fields
                              `((,misc-name     :initially nil)
                                (,good-name     :initially t)
                                (,badplace-name :initially nil))
                              (make-arr-rec-fields ftas)))
       (args          (append st-fields+ st-kw-part))
       (st-form       `(defstobj ,name ,@args))

       ;; Regenerate the templates that the extended form will use, so that
       ;; we'll have FTAs for the array records and the other extra fields.
       (ext-st-template (defstobj-template name args wrld))
       ((list & & ext-st-fld-templates & &)
        (destructure-defstobj-template ext-st-template))
       (ext-ftas (make-ftas (strip-cars st-fields+) ext-st-fld-templates tr-alist mksym-pkg))

       (misc-fta           (find-fta misc-name ext-ftas))
       (good-fta           (find-fta good-name ext-ftas))
       (badplace-fta       (find-fta badplace-name ext-ftas))
       (st-misc            (cdr (assoc :accessor-name misc-fta)))
       (update-st-good     (cdr (assoc :updater-name good-fta)))
       (update-st-badplace (cdr (assoc :updater-name badplace-fta)))
       (st-badplace        (cdr (assoc :accessor-name badplace-fta)))

       (st-fns   (list* namep create-name (fta-list-fns ext-ftas)))

       (badguy1 (mksym name '-BADGUY1))
       (badguy  (mksym name '-BADGUY))

       )

    `(with-output
       :off (summary)
       (encapsulate
         ()

; Get into a very restricted theory that (hopefully) just includes what we need.

         (logic)
         (set-inhibit-warnings "non-rec" "disable" "subsume") ;; implicitly local
         (local (set-default-hints nil))
         (local (include-book "projects/legacy-defrstobj/array-lemmas" :dir :system))
         (local (in-theory
                 (union-theories
                  (union-theories (theory 'minimal-theory)
                                  (theory 'array-lemmas))
                  (executable-counterpart-theory :here))))

         ;; This could generate huge lists if someone asks for a big array
         (local (in-theory (disable (:executable-counterpart make-list-ac))))

         (local (in-theory (enable not o< o-finp acl2-count zp natp nfix max
                                   len length true-listp update-nth-array

                                   acl2::natp-compound-recognizer
                                   car-cons cdr-cons car-cdr-elim

                                   nth-0-cons
                                   nth-add1
                                   len-update-nth
                                   nth-update-nth
                                   true-listp-update-nth
                                   non-executable-nth

                                   acl2::s-diff-s
                                   acl2::s-same-s
                                   acl2::s-same-g
                                   acl2::g-diff-s
                                   acl2::g-same-s
                                   acl2::g-of-nil-is-nil
                                   g-of-g-delete-keys
                                   g-delete-keys-of-s-diff

                                   (:type-prescription true-listp)
                                   (:type-prescription len)
                                   (:type-prescription acl2-count)

                                   ,@(collect-typed-record-thms ftas wrld))))

         ,st-form

         (in-theory (disable ,@st-fns))

         (local (in-theory (enable ,@st-fns)))

         (local (progn ,@(array-boilerplate ftas mksym-pkg wrld)))

         (defthm ,(mksym namep '-of- create-name)
           (,namep (,create-name))
           :hints (("Goal"
                    :in-theory (e/d (,namep ,create-name)
                                    (make-list-ac (make-list-ac))))))

         (defund-nx ,weak-stp (,name)
           (and (true-listp ,name)
                (= (len ,name) ,(len st-fields+))
                ,@(weak-stp-conjuncts name ftas wrld)
                ;; In support of equal-by-keys, we now require that the misc
                ;; field must not mention the other keys.
                (let ((misc (,st-misc ,name)))
                  (equal misc (g-delete-keys ',user-keys misc)))))

         (local (in-theory (enable ,weak-stp
                                   ,@(collect-array-rec-pair-ps ftas wrld))))

         (defund ,good-stp (,name)
           (declare (xargs :stobjs ,name))
           (mbe :logic (and (,weak-stp ,name)
                            (eq (,good-name ,name) t))
                :exec (and (eq (,good-name ,name) t)
                           ,@(good-stp-conjuncts name ftas wrld)
                           ;; In support of equal-by-keys, we now require that
                           ;; the misc field must not mention the other keys.
                           (let ((misc (,st-misc ,name)))
                             (equal misc (g-delete-keys ',user-keys misc))))))


         ;; Matt Kaufmann sent me a nice bug report that showed
         ;; good-stp-of-create-st failing for an extremely simple rstobj.  It
         ;; seemed like ACL2 was trying to prove the theorem by executing
         ;; good-stp on the constant list '(0 nil t nil), which was getting
         ;; created by (create-st).  But this in turn called weak-stp, which is
         ;; non-executable, and wrapped the whole term in a HIDE.  Then nothing
         ;; could apply to it, and everything broke down.  So, to fix this,
         ;; just make sure we never try to execute these during the following
         ;; proofs.  See "matt-example" in basic-tests.lisp.
         (local (in-theory (disable (:executable-counterpart ,good-stp)
                                    (:executable-counterpart ,weak-stp))))

         (defthm ,(mksym good-stp '-of- create-name)
           (,good-stp (,create-name))
           :hints(("Goal" :in-theory (enable ,good-stp))))

         ;; The wrappers for reading/writing individual array fields
         ,@(array-update-wrappers name ftas mksym-pkg wrld)

         ;; Proofs that the individual wrappers don't interfere with one another
         (local ,(make-noninterference-top name ftas mksym-pkg))

         ;; The get1/set1 wrappers for dealing with arbitrary fields
         ,(make-st-wrappers name ftas misc-fta mksym-pkg
                            good-name update-st-good
                            badplace-name update-st-badplace)

         (local (in-theory (disable ,create-name)))

         (defund-nx ,bad-stp (,name)
           (declare (xargs :hints (("Goal" :in-theory (enable nth)))))
           (or (not (,weak-stp ,name))
               (and (not (eq (,good-name ,name) t))
                    (,bad-stp (,badplace-name ,name))
                    (let* ((temp (,create-name))
                           (temp (,update-st-good nil temp))
                           (temp (,update-st-badplace (,st-badplace ,name) temp)))
                      (equal ,name temp)))))

         (local (in-theory (enable ,bad-stp)))

         (local (defthm ,(mksym 'not- bad-stp '-when- good-stp)
                  (implies (,good-stp ,name)
                           (not (,bad-stp ,name)))
                  :hints(("Goal" :in-theory (enable ,good-stp)))))

         (defund-nx ,to (,name)
           (if (,bad-stp ,name)
               (let* ((temp (,create-name))
                      (temp (,update-st-badplace ,name temp))
                      (temp (,update-st-good nil temp)))
                 temp)
             ,name))

         (defund-nx ,from (,name)
           (if (,bad-stp ,name)
               (,st-badplace ,name)
             ,name))

         (encapsulate
           ()
           (local (in-theory (enable ,to ,from)))

           (defthm ,(mksym to '-identity)
             (implies (not (,bad-stp ,name))
                      (equal (,to ,name)
                             ,name)))

           (defthm ,(mksym weak-stp '-of- to)
             (,weak-stp (,to ,name))
             :hints(("Goal" :in-theory (enable ,create-name))))

           (defthm ,(mksym from '-identity)
             (implies (not (,bad-stp ,name))
                      (equal (,from ,name)
                             ,name)))

           (defthm ,(mksym from '- to '-inverse)
             (equal (,from (,to ,name))
                    ,name))

           (defthm ,(mksym to '- from '-inverse)
             (implies (,weak-stp ,name)
                      (equal (,to (,from ,name))
                             ,name))))


         ;; The main logical story

         (defund-nx ,get (key ,name)
           (,get1 key (,to ,name)))

         (defund-nx ,set (key val ,name)
           (,from (,set1 key val (,to ,name))))

         (local (in-theory (enable ,get ,set)))

         (defthm ,(mksym good-stp '-of- set)
           (implies (and (force (,good-stp ,name))
                         (force (not (equal key :rstobj-good))))
                    (,good-stp (,set key val ,name))))

         (defthm ,(mksym get '-of- set '-same)
           (equal (,get key (,set key val ,name))
                  val))

         (defthm ,(mksym get '-of- set '-diff)
           (implies (not (equal key1 key2))
                    (equal (,get key1 (,set key2 val ,name))
                           (,get key1 ,name))))

         (defthm ,(mksym set '-of- get '-same)
           (equal (,set key1 (,get key1 ,name) ,name)
                  ,name))

         (defthm ,(mksym set '-of- set '-diff)
           (implies (not (equal key1 key2))
                    (equal (,set key1 val1 (,set key2 val2 ,name))
                           (,set key2 val2 (,set key1 val1 ,name))))
           ;; ACL2 infers a bad loop stopper otherwise (it considers the values
           ;; instead of just the keys!)
           :rule-classes ((:rewrite :loop-stopper ((key1 key2)))))

         (defthm ,(mksym set '-of- set '-same)
           (equal (,set key val1 (,set key val2 ,name))
                  (,set key val1 ,name)))

         ;; We leave the strong rule enabled even though it may be too
         ;; expensive in general.  If you disable it, you'll still have the
         ;; weaker -SAME and -DIFF rules unless you disable them, too.
         (defthm ,(mksym get '-of- set '-strong)
           (equal (,get key1 (,set key2 val ,name))
                  (if (equal key1 key2)
                      val
                    (,get key1 ,name))))

         (local (in-theory (disable ,get ,set)))

         ;; Main functions for execution

         (local (in-theory (enable ,good-stp
                                   ,get
                                   ,set
                                   ,get1
                                   ,set1)))

         ,@(make-exec-getters name ftas mksym-pkg wrld)
         ,@(make-exec-setters name ftas mksym-pkg wrld)



; Development of EQUAL-BY-G style reasoning

         (local (in-theory (enable fancy-worseguy-finds-counterexample
                                   fancy-worseguy-not-among-keys
                                   fancy-worseguy-unless-equal)))

         (defsection ,badguy1

           (defund-nx ,badguy1 (x y)
             (cond
              ,@(make-cond-pairs-for-badguy1 get1 user-keys)
              (t (fancy-worseguy ',user-keys
                                 (,misc-name x)
                                 (,misc-name y)))))

           (local (in-theory (enable ,badguy1 ,get1)))

; Critical fact 1: If the badguy finds something, then it's different between
; the two stobjs.

           (defthm ,(mksym badguy1 '-finds-counterexample)
             (implies (,badguy1 x y)
                      (equal (equal (,get1 (cadr (,badguy1 x y)) x)
                                    (,get1 (cadr (,badguy1 x y)) y))
                             nil)))

; Critical fact 2: If the two stobjs are well-formed and not equal, then the
; badguy finds something.  We start by showing that any difference in a
; particular field will be exposed by our new badguy.

           ,@(badguy-finds-diffs-lemmas name badguy1 weak-stp ftas wrld)

           (local (defthm badguy1-finds-diffs-in-good
                    (implies (not (equal (,good-name x) (,good-name y)))
                             (,badguy1 x y))))

           (local (defthm badguy1-finds-diffs-in-badplace
                    (implies (not (equal (,badplace-name x) (,badplace-name y)))
                             (,badguy1 x y))))

           (local (defthm badguy1-finds-diffs-in-misc
                    (implies (and (,weak-stp x)
                                  (,weak-stp y)
                                  (not (equal (,misc-name x) (,misc-name y))))
                             (,badguy1 x y))
                    :hints(("Goal" :in-theory (enable ,weak-stp)))))

           (local (defthm equal-when-weak-stp
                    (implies (and (,weak-stp x)
                                  (,weak-stp y))
                             (equal (equal x y)
                                    (and (equal (,good-name x) (,good-name y))
                                         (equal (,misc-name x) (,misc-name y))
                                         (equal (,badplace-name x) (,badplace-name y))
                                         ,@(equal-when-weak-stp-rhs ftas))))
                    :hints(("Goal" :in-theory (enable equal-of-cons-rewrite
                                                      expand-nth
                                                      equal-len-with-constant
                                                      ,weak-stp)))))

           (defthm ,(mksym badguy1 '-unless-equal)
             (implies (and (not (equal x y))
                           (,weak-stp x)
                           (,weak-stp y))
                      (,badguy1 x y))
             :hints(("Goal" :in-theory (e/d (,get1)
                                            (,badguy1))))))

         (defsection ,badguy

           (defund-nx ,badguy (x y)
             (,badguy1 (,to x) (,to y)))

           (local (in-theory (enable ,badguy)))

           (local (defthm weak-unless-bad
                    (implies (not (,bad-stp x))
                             (,weak-stp x))
                    :hints(("Goal" :in-theory (enable ,bad-stp)))))

           (local (defthm badplace-of-to-when-bad
                    (implies (,bad-stp x)
                             (equal (,badplace-name (,to x))
                                    x))
                    :hints(("Goal" :in-theory (enable ,to
                                                      ,badplace-name
                                                      ,update-st-good
                                                      ,update-st-badplace)))))

           (local (defthm to-leaves-nonbad-alone
                    (implies (not (,bad-stp x))
                             (equal (,to x)
                                    x))))

           (local (defthm to-leaves-bad-bad
                    (implies (,bad-stp x)
                             (,bad-stp (,to x)))
                    :hints(("Goal" :in-theory (enable ,bad-stp
                                                      ,to
                                                      ,good-name
                                                      ,badplace-name
                                                      ,update-st-good
                                                      ,update-st-badplace
                                                      ,create-name)))))

           (defthm ,(mksym badguy '-finds-counterexample)
             (implies (,badguy x y)
                      (equal (equal (,get (cadr (,badguy x y)) x)
                                    (,get (cadr (,badguy x y)) y))
                             nil))
             :hints(("Goal"
                     :use ((:instance ,(mksym badguy1 '-finds-counterexample)
                                      (x (,to x))
                                      (y (,to y)))))))

           (local (defthm lemma-both-good
                    (implies (and (not (equal x y))
                                  (case-split (not (,bad-stp x)))
                                  (case-split (not (,bad-stp y))))
                             (,badguy x y))))

           (local (defthm bad-still-differ
                    (implies (and (not (equal x y))
                                  (,bad-stp x)
                                  (,bad-stp y))
                             (not (equal (,to x) (,to y))))
                    :hints(("Goal"
                            :do-not '(generalize fertilize eliminate-destructors)
                            :do-not-induct t
                            :in-theory (disable badplace-of-to-when-bad)
                            :use ((:instance badplace-of-to-when-bad (x x))
                                  (:instance badplace-of-to-when-bad (x y)))))))

           (local (defthm lemma-both-bad
                    (implies (and (not (equal x y))
                                  (case-split (,bad-stp x))
                                  (case-split (,bad-stp y)))
                             (,badguy x y))
                    :hints(("Goal"
                            :do-not '(generalize fertilize eliminate-destructors)
                            :do-not-induct t
                            :in-theory (disable ,(mksym badguy1 '-unless-equal))
                            :use ((:instance ,(mksym badguy1 '-unless-equal)
                                             (x (,to x))
                                             (y (,to y))))))))

           (local (defthm lemma-bad-with-good
                    (implies (and (not (equal x y))
                                  (case-split (,bad-stp x))
                                  (case-split (not (,bad-stp y))))
                             (,badguy x y))
                    :hints(("Goal"
                            :in-theory (disable ,(mksym badguy1 '-unless-equal))
                            :use ((:instance ,(mksym badguy1 '-unless-equal)
                                             (x (,to x))
                                             (y (,to y))))))))

           (local (defthm lemma-good-with-bad
                    (implies (and (not (equal x y))
                                  (case-split (,bad-stp x))
                                  (case-split (not (,bad-stp y))))
                             (,badguy y x))
                    :hints(("Goal"
                            :in-theory (disable ,(mksym badguy1 '-unless-equal))
                            :use ((:instance ,(mksym badguy1 '-unless-equal)
                                             (x (,to y))
                                             (y (,to x))))))))

           (defthm ,(mksym badguy '-unless-equal)
             (implies (not (equal x y))
                      (,badguy x y))
             :hints(("Goal" :in-theory (disable ,badguy)))))


         ;; Fancy rule for equalities of set-nests.  See the discussion of
         ;; EQUAL-OF-TR-SET in typed-records.lisp for an explanation of this
         ;; rule.
         (defthm ,(mksym 'equal-of- set)
           (implies
            (syntaxp (or (acl2::rewriting-positive-literal-fn
                          (list 'equal (list ',set key val x) y)
                          mfc state)
                         (acl2::rewriting-positive-literal-fn
                          (list 'equal y (list ',set key val x))
                          mfc state)))
            (equal (equal (,set key val x) y)
                   (let ((arb (acl2::introduce-var 'arbitrary-key
                                                   (hide (cadr (,badguy (,set key val x) y))))))
                     (equal (,get arb (,set key val x))
                            (,get arb y)))))
           :hints(("Goal"
                   :expand (:free (x) (hide x))
                   :in-theory (e/d (acl2::introduce-var)
                                   (,badguy ,get ,set
                                    ,(mksym badguy '-finds-counterexample)
                                    ,(mksym badguy '-unless-equal)))
                   :use ((:instance ,(mksym badguy '-finds-counterexample)
                                    (x (,set key val x))
                                    (y y))
                         (:instance ,(mksym badguy '-unless-equal)
                                    (x (,set key val x))
                                    (y y))))))



         (value-triple ',name)))))

(defmacro defrstobj (name &rest args)
  `(make-event
    (defrstobj-fn ',name ',args (w state))))

