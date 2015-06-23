; Hash Tables in Stobjs
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/alists/hons-remove-assoc" :dir :system)

;; Support for stobjs with hash table members.
;; To extend the example used in defstobj:

#|


(defstobj $st
    (flag :type t :initially run)
    (pctr   :type (integer 0 255) :initially 128)
    (mem  :type (array (integer 0 255) (256)) :initially 0)
    (tab :type (hash-table eql)))

(defstobj equalht
  (equaltab :type (hash-table equal)))

(defstobj hons-equalht
  (hons-equaltab :type (hash-table hons-equal)))



|#

;; Since array members are represented by lists, we'll represent hash
;; table members as alists, as illustrated below.

;; Is this sound?  See the theorems proven below about the
;; interactions of the logical definitions of the access and update
;; functions.  I argue that these theorems are exactly the contract of
;; a hash table (provided that the inputs are well-formed,
;; i.e. EQLABLE for an EQL table, etc).  If this is the case, then
;; this is only unsound in the event that the underlying Lisp has a
;; bug in its hash table implementation.

;; We make guards on these functions as weak as possible since they
;; have nothing to do with the performance in raw Lisp, and arguably
;; we care more about ease of proving guard conjectures than we do
;; about how well they perform in the logic.


(local (in-theory (enable hons-remove-assoc)))

(defthm hons-remove-assoc-acl2-count-weak
  (<= (acl2-count (hons-remove-assoc x al)) (acl2-count al))
  :rule-classes :linear)

(defun count-keys (al)
  (declare (xargs :guard t))
  (if (atom al)
      0
    (if (consp (car al))
        (+ 1 (count-keys (hons-remove-assoc (caar al) (cdr al))))
      (count-keys (cdr al)))))

(defthm not-assoc-hons-remove-assoc
  (not (hons-assoc-equal k (hons-remove-assoc k al))))

(defthm assoc-hons-remove-assoc-diff
  (implies (not (equal j k))
           (equal (hons-assoc-equal k (hons-remove-assoc j al))
                  (hons-assoc-equal k al))))

(defthm hons-remove-assoc-repeat
  (equal (hons-remove-assoc k (hons-remove-assoc k al))
         (hons-remove-assoc k al)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm count-keys-hons-remove-assoc
  (equal (count-keys (hons-remove-assoc k al))
         (if (consp (hons-assoc-equal k al))
             (1- (count-keys al))
           (count-keys al))))

(defthm count-keys-cons
  (equal (count-keys (cons (cons k v) al))
         (if (consp (hons-assoc-equal k al))
             (count-keys al)
           (+ 1 (count-keys al)))))


#||

;; Using this example stobj definition, we'll illustrate the logical
;; definitions of the functions used to access and update the table.

(defstobj htable
  (tab :type (hash-table eql))) ;; or (hash-table equal)

(defun tabp
  (declare (xargs :guard t))
  ;; Because we made the guards on hons-assoc-equal and hons-remove-assoc T, we
  ;; don't need to constrain what tabp is logically.
  t)

(defun htablep (x)
  (declare (xargs :guard t))
  (true-listp x))

;; CREATE-HTABLE:
(defun create-htable ()
  (declare (xargs :guard t))
  (list nil))

;; GET, logic:
(defun tab-get (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (cdr (hons-assoc-equal k (nth 0 htable))))

;; BOUNDP, logic:
(defun tab-boundp (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (consp (hons-assoc-equal k (nth 0 htable))))

;; GET?, logic:
(defun tab-get? (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (mv (tab-get k htable)
      (tab-boundp k htable)))

;; PUT, logic:
(defun tab-put (k v htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (update-nth 0 (cons (cons k v)
                      (nth 0 htable)) htable))

;; REM, logic:
(defun tab-rem (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (update-nth 0 (hons-remove-assoc k (nth 0 htable)) htable))

;; COUNT, logic:
(defun tab-count (htable)
  (count-keys (nth 0 htable)))

;; CLEAR, logic:
(defun tab-clear (htable)
  (declare (xargs :guard (htablep htable)))
  (update-nth 0 nil htable))

(defun tab-init (size rehash-size rehash-threshold htable)
  (declare (xargs :guard (and (htablep htable)
                              (or (natp size)
                                  (not size))
                              (or (and (rationalp rehash-size)
                                       (< 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold)))))
  (declare (ignore size rehash-size rehash-threshold))
  (update-nth 0 nil htable))

;; Theorems about the interactions of the functions above: Our
;; approach is sound if these theorems completely and accurately model
;; the functionality of a Common Lisp hash table, modulo assumptions
;; about what keys are allowed.  We can argue that these are complete
;; since we can completely specify the values of any of the accessors
;; (tab-get, tab-boundp, tab-count) on any nesting of the updaters
;; (tab-put, tab-rem), by induction:
;; Base case 1: empty table; tab-get and tab-boundp both return nil.
;; Base case 2: (tab-put k v htable), where k is the key being
;; searched for:  tab-get returns v, tab-boundp returns t.
;; Base case 3: (tab-rem k htable), where k is the key being searched
;; for: tab-get and tab-boundp again both return nil.
;; Base case 4: (tab-clear htable): both return nil.
;; Induction case 1: (tab-put j v htable), j not equal k, reduces to
;; access of htable,
;; Induction case 2: (tab-rem j htable), j not equal k, reduces to
;; access of htable.

(defthm tab-init-is-tab-clear
  (equal (tab-init size rehash-size rehash-threshold htable)
         (tab-clear htable)))

(defthm tab-get-tab-boundp
  (implies (tab-get k htable)
           (tab-boundp k htable)))

(defthm tab-boundp-start
  (not (tab-boundp k (create-htable))))

(defthm tab-boundp-clear
  (not (tab-boundp k (tab-clear htable))))

(defthm tab-boundp-tab-put-same
  (tab-boundp k (tab-put k v htable)))

(defthm tab-boundp-tab-put-diff
  (implies (not (equal j k))
           (equal (tab-boundp k (tab-put j v htable))
                  (tab-boundp k htable))))

(defthm tab-get-tab-put-same
  (equal (tab-get k (tab-put k v htable))
         v))

(defthm tab-get-tab-put-diff
  (implies (not (equal j k))
           (equal (tab-get k (tab-put j v htable))
                  (tab-get k htable))))

(defthm tab-rem-tab-boundp-same
  (not (tab-boundp k (tab-rem k htable))))

(defthm tab-rem-tab-boundp-diff
  (implies (not (equal j k))
           (equal (tab-boundp k (tab-rem j htable))
                  (tab-boundp k htable))))

(defthm tab-rem-tab-get-diff
  (implies (not (equal j k))
           (equal (tab-get k (tab-rem j htable))
                  (tab-get k htable))))

(defthm tab-count-start
  (equal (tab-count (create-htable)) 0))

(defthm tab-count-put
  (equal (tab-count (tab-put k v htable))
         (if (tab-boundp k htable)
             (tab-count htable)
           (+ 1 (tab-count htable)))))

(defthm tab-count-rem
  (equal (tab-count (tab-rem k htable))
         (if (tab-boundp k htable)
             (- (tab-count htable) 1)
           (tab-count htable))))

(defthm tab-count-clear
  (equal (tab-count (tab-clear htable)) 0))

;; CREATE-HTABLE, raw:
(defun create-htable ()
  (vector (make-hash-table :test 'eql)))

;; GET, raw:
(defun tab-get (k htable)
  ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
  (values (gethash k
                   (svref htable 0))))
;; BOUNDP, raw:
(defun tab-boundp (k htable)
  (multiple-value-bind (ans boundp)
      ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
      (gethash k (svref htable 0))
    (declare (ignore ans))
    boundp))
;; GET?, raw:
(defun tab-get? (k htable)
  ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
  (gethash k (svref htable 0)))

;; PUT, raw:
(defun tab-put (k v htable)
  ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
  (setf (gethash k (svref htable 0)) v)
  htable)

;; REM, raw:
(defun tab-rem (k htable)
  ;; replace K with (HONS-COPY K) in HONS-EQUAL version
  (remhash k (svref htable 0))
  htable)

;; COUNT, raw:
(defun tab-count (htable)
  (hash-table-count (svref htable 0)))

(defun tab-clear (htable)
  (clrhash (svref htable 0))
  htable)

(defun tab-init (size rehash-size rehash-threshold htable)
  (setf (svref htable 0)
        (make-hash-table
         :size (or size 60)
         :rehash-size (if rehash-size
                          (float rehash-size)
                        (float 17/10))
         :rehash-threshold (if rehash-threshold
                               (float rehash-threshold)
                             (float 3/4))))
  htable)

||#




(defttag hash-stobjs)

(program)
(set-state-ok t)

(redef+)
(defun defstobj-fnname (root key1 key2 renaming-alist)

; Warning: Keep this in sync with stobj-updater-guess-from-accessor.

; This has been moved from other-events.lisp, where other stobj-related
; functions are defined, because it is used in parse-with-local-stobj, which is
; used in translate11.

; This function generates the actual name we will use for a function generated
; by defstobj.  Root and renaming-alist are, respectively, a symbol and an
; alist.  Key1 describes which function name we are to generate and is one of
; :length, :resize, :recognizer, :accessor, :updater, or :creator.  Key2
; describes the ``type'' of root.  It is :top if root is the name of the live
; object (and hence, root starts with a $) and it is otherwise either :array or
; :non-array.  Note that if renaming-alist is nil, then this function returns
; the ``default'' name used.  If renaming-alist pairs some default name with an
; illegal name, the result is, of course, an illegal name.

  (let* ((default-fnname
           (case key1
             (:recognizer
              (case key2
                (:top
                 (packn-pos
                  (list (coerce (append (coerce (symbol-name root) 'list)
                                        '(#\P))
                                'string))
                  root))
                (otherwise (packn-pos (list root "P") root))))

; This function can legitimately return nil for key1 values of :length
; and :resize.  We are careful in the assoc-eq call below not to look
; for nil on the renaming-alist.  That check is probably not
; necessary, but we include it for robustness.

             (:length
              (and (eq key2 :array)
                   (packn-pos (list root "-LENGTH") root)))
             (:resize
              (and (eq key2 :array)
                   (packn-pos (list "RESIZE-" root) root)))
             (:accessor
              (case key2
                (:array (packn-pos (list root "I") root))
;---<
                (:hash-table (packn-pos (list root "-GET") root))
;   >---
                (otherwise root)))
             (:updater
              (case key2
                (:array (packn-pos (list "UPDATE-" root "I") root))
;---<
                (:hash-table (packn-pos (list root "-PUT") root))
;   >---
                (otherwise (packn-pos (list "UPDATE-" root) root))))
             (:creator
              (packn-pos (list "CREATE-" root) root))
;---<
             (:boundp 
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-BOUNDP") root)))
             (:accessor?
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-GET?") root)))
             (:remove
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-REM") root)))
             (:count
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-COUNT") root)))
             (:init
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-INIT") root)))
             (:clear
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-CLEAR") root)))
;   >---
             (otherwise
              (er hard 'defstobj-fnname
                  "Implementation error (bad case); please contact ACL2 ~
                   implementors."))))
         (temp (and default-fnname ; see comment above
                    (assoc-eq default-fnname renaming-alist))))
    (if temp (cadr temp) default-fnname)))



(defun defstobj-field-templates (field-descriptors renaming wrld)

; Note: Wrld may be a world or nil.  See fix-stobj-array-type.

  (cond
   ((endp field-descriptors) nil)
   (t
    (let* ((field-desc (car field-descriptors))
           (field (if (atom field-desc)
                      field-desc
                    (car field-desc)))
           (type (if (consp field-desc)
                     (or (cadr (assoc-keyword :type (cdr field-desc)))
                         t)
                   t))
           (init (if (consp field-desc)
                     (cadr (assoc-keyword :initially (cdr field-desc)))
                   nil))
           (resizable (if (consp field-desc)
                          (cadr (assoc-keyword :resizable (cdr field-desc)))
                        nil))
;---<
           (key2 (if (consp type)
                     (case (car type)
                       (array :array)
                       (hash-table :hash-table)
                       (t :non-array))
                   :non-array))
;   >---
           (fieldp-name (defstobj-fnname field :recognizer key2 renaming))
           (accessor-name (defstobj-fnname field :accessor key2 renaming))
           (updater-name (defstobj-fnname field :updater key2 renaming))
;---<
           (boundp-name (defstobj-fnname field :boundp key2 renaming))
           (accessor?-name (defstobj-fnname field :accessor? key2
                             renaming))
           (remove-name (defstobj-fnname field :remove key2 renaming))
           (count-name (defstobj-fnname field :count key2 renaming))
           (clear-name (defstobj-fnname field :clear key2 renaming))
           (init-name (defstobj-fnname field :init key2 renaming))
;   >---
           (resize-name (defstobj-fnname field :resize key2 renaming))
           (length-name (defstobj-fnname field :length key2 renaming)))
      (cons (make defstobj-field-template
                  :fieldp-name fieldp-name
                  :type (cond ((and (consp type)
                                    (eq (car type) 'array))
                               (fix-stobj-array-type type wrld))
                              (t type))
                  :init init
                  :accessor-name accessor-name
                  :updater-name updater-name
                  :length-name length-name
                  :resize-name resize-name
                  :resizable resizable
;---<
                  :other
                  (list boundp-name
                        accessor?-name
                        remove-name
                        count-name
                        clear-name
                        init-name)
;   >---
                  )
            (defstobj-field-templates
              (cdr field-descriptors) renaming wrld))))))

(defun defstobj-raw-init-fields (field-templates)

; Keep this in sync with defstobj-axiomatic-init-fields.

  (cond
   ((endp field-templates) nil)
   (t (let* ((field-template (car field-templates))
             (type (access defstobj-field-template field-template :type))
             (arrayp (and (consp type) (eq (car type) 'array)))
;---<
             (hashp (and (consp type) (eq (car type) 'hash-table)))
             (hash-test (and hashp (cadr type)))
             (hash-init-size (and hashp (if (cddr type)
                                            (caddr type)
                                          20)))
;   >---
             (array-etype0 (and arrayp (cadr type)))
             (array-size (and arrayp (car (caddr type))))
             (stobj-creator (get-stobj-creator (if arrayp array-etype0 type)
                                               nil))
             (array-etype (and arrayp

; See comment for this binding in defstobj-field-fns-raw-defs.

                               (if stobj-creator
                                   t
                                 array-etype0)))
             (init (access defstobj-field-template field-template :init)))
        (cond
         (arrayp
          (cons (cond (stobj-creator
                       (assert$
                        (null init) ; checked by chk-stobj-field-descriptor
                        (assert$

; We expect array-size to be a natural number, as this is checked by
; chk-stobj-field-descriptor (using fix-stobj-array-type).  It is important
; that array-size not be a Lisp form that references the variable AR, even
; after macroexpasion, in order to avoid capture by the binding of AR below.

                         (natp array-size)
                         `(let ((ar (make-array$ ,array-size

; Do not be tempted to use :initial-element (,stobj-creator) here, because that
; would presumably share structure among all the created stobjs.

                                                 :element-type ',array-etype)))
                            (loop for i from 0 to ,(1- array-size)
                                  do
                                  (setf (svref ar i) (,stobj-creator)))
                            ar))))
                      (t `(make-array$ ,array-size
                                       :element-type ',array-etype
                                       :initial-element ',init)))
                (defstobj-raw-init-fields (cdr field-templates))))
;---<
         (hashp
          (cons `(make-hash-table
                  :test
                  ,(case hash-test
                     (eql ''eql)
                     (equal
                      ;; Is this safe?
                      ''equal)
                     (t (er hard hash-test
                            "The hash test should be either EQL or EQUAL.~%")))
                  :size ,hash-init-size)
                (defstobj-raw-init-fields (cdr field-templates))))
;   >---
         ((eq type t)
          (cons (kwote init)
                (defstobj-raw-init-fields (cdr field-templates))))
         (stobj-creator
          (cons `(,stobj-creator)
                (defstobj-raw-init-fields (cdr field-templates))))
         (t (cons `(make-array$ 1
                                :element-type ',type
                                :initial-element ',init)
                  (defstobj-raw-init-fields (cdr field-templates)))))))))

(defun defstobj-component-recognizer-axiomatic-defs (name template
                                                          field-templates wrld)

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

; It is permissible for wrld to be nil, as this merely defeats additional
; checking by translate-declaration-to-guard.

; We return a list of defs (see defstobj-axiomatic-defs) for all the
; recognizers for the single-threaded resource named name with the given
; template.  The answer contains the top-level recognizer as well as the
; definitions of all component recognizers.  The answer contains defs for
; auxiliary functions used in array component recognizers.  The defs are listed
; in an order suitable for processing (components first, then top-level).

  (cond
   ((endp field-templates)
    (let* ((recog-name (access defstobj-template template :recognizer))
           (field-templates (access defstobj-template template
                                    :field-templates))
           (n (length field-templates)))

; Rockwell Addition: See comment below.

; Note: The recognizer for a stobj must be Boolean!  That is why we
; conclude the AND below with a final T.  The individual field
; recognizers need not be Boolean and sometimes are not!  For example,
; a field with :TYPE (MEMBER e1 ... ek) won't be Boolean, nor with
; certain :TYPE (OR ...) involving MEMBER.  The reason we want the
; stobj recognizer to be Boolean is so that we can replace it by T in
; guard conjectures for functions that have been translated with the
; stobj syntactic restrictions.  See optimize-stobj-recognizers.

      (list `(,recog-name (,name)
                          (declare (xargs :guard t
                                          :verify-guards t))
                          (and (true-listp ,name)
                               (= (length ,name) ,n)
                               ,@(defstobj-component-recognizer-calls
                                   field-templates 0 name nil)
                               t)))))
   (t
    (let ((recog-name (access defstobj-field-template
                              (car field-templates)
                              :fieldp-name))
          (type (access defstobj-field-template
                        (car field-templates)
                        :type)))

; Below we simply append the def or defs for this field to those for
; the rest.  We get two defs for each array field and one def for each
; of the others.

      (cons (cond
             ((and (consp type)
                   (eq (car type) 'array))
              (let ((etype (cadr type)))
                `(,recog-name (x)
                              (declare (xargs :guard t
                                              :verify-guards t))
                              (if (atom x)
                                  (equal x nil)
                                (and ,(translate-stobj-type-to-guard
                                       etype '(car x) wrld)
                                     (,recog-name (cdr x)))))))
;---<
             ((and (consp type)
                   (eq (car type) 'hash-table))
              `(,recog-name (x)
                            (declare (xargs :guard t
                                            :verify-guards t)
                                     (ignore x))
                            t))
;   >---
             (t (let ((type-term (translate-stobj-type-to-guard
                                  type 'x wrld)))

; We might not use x in the type-term and so have to declare it ignorable.

                  `(,recog-name (x)
                                (declare (xargs :guard t
                                                :verify-guards t)
                                         (ignorable x))
                                ,type-term))))
            (defstobj-component-recognizer-axiomatic-defs
              name template (cdr field-templates) wrld))))))

(defun defstobj-field-fns-axiomatic-defs (top-recog var n field-templates wrld)

; Wrld is normally a logical world, but it can be nil when calling this
; function from raw Lisp.

; Warning: Keep the formals in the definitions below in sync with corresponding
; formals defstobj-field-fns-raw-defs.  Otherwise trace$ may not work
; correctly; we saw such a problem in Version_5.0 for a resize function.

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

; We return a list of defs (see defstobj-axiomatic-defs) for all the accessors,
; updaters, and optionally, array resizing and length, of a single-threaded
; resource.

; Warning: Each updater definition should immediately follow the corresponding
; accessor definition, so that this is the case for the list of definitions
; returned by defstobj-axiomatic-defs.  That list of definitions becomes the
; 'stobj property laid down by defstobj-fn, and function
; chk-stobj-let/updaters1 assumes that it will find each updater definition in
; that property immediately after the corresponding accessor definition.

  (cond
   ((endp field-templates)
    nil)
   (t (let* ((field-template (car field-templates))
             (type (access defstobj-field-template
                           field-template
                           :type))
             (arrayp (and (consp type) (eq (car type) 'array)))
             (init0 (access defstobj-field-template
                            field-template
                            :init))
             (creator (get-stobj-creator (if arrayp (cadr type) type)
                                         wrld))
             (init (if creator
                       `(non-exec (,creator))
                     (kwote init0)))
;---<
             (hashp (and (consp type) (eq (car type) 'hash-table)))
             (hash-test (and hashp (cadr type)))
;   >---
             (type-term            ; used in guard
              (and (not arrayp)    ; else type-term is not used
;---<
                   (not hashp)
;   >---
                   (if (null wrld) ; called from raw Lisp, so guard is ignored
                       t
                     (translate-stobj-type-to-guard type 'v wrld))))
             (array-etype (and arrayp (cadr type)))
             (array-etype-term     ; used in guard
              (and arrayp          ; else array-etype-term is not used
                   (if (null wrld) ; called from raw Lisp, so guard is ignored
                       t
                     (translate-stobj-type-to-guard array-etype 'v wrld))))
             (array-length (and arrayp (car (caddr type))))
             (accessor-name (access defstobj-field-template
                                    field-template
                                    :accessor-name))
             (updater-name (access defstobj-field-template
                                   field-template
                                   :updater-name))
             (length-name (access defstobj-field-template
                                  field-template
                                  :length-name))
             (resize-name (access defstobj-field-template
                                  field-template
                                  :resize-name))
             (resizable (access defstobj-field-template
                                field-template
                                :resizable))
;---<
             (other (access defstobj-field-template
                            field-template
                            :other))
             (boundp-name (nth 0 other))
             (accessor?-name (nth 1 other))
             (remove-name (nth 2 other))
             (count-name (nth 3 other))
             (clear-name (nth 4 other))
             (init-name (nth 5 other))
;   >---
             )
        (cond
         (arrayp
          (append
           `((,length-name (,var)
                           (declare (xargs :guard (,top-recog ,var)
                                           :verify-guards t)
                                    ,@(and (not resizable)
                                           `((ignore ,var))))
                           ,(if resizable
                                `(len (nth ,n ,var))
                              `,array-length))
             (,resize-name
              (i ,var)
              (declare (xargs :guard (,top-recog ,var)
                              :verify-guards t)
                       ,@(and (not resizable)
                              '((ignore i))))
              ,(if resizable
                   `(update-nth ,n
                                (resize-list (nth ,n ,var) i ,init)
                                ,var)
                 `(prog2$ (hard-error
                           ',resize-name
                           "The array field corresponding to accessor ~x0 of ~
                            stobj ~x1 was not declared :resizable t.  ~
                            Therefore, it is illegal to resize this array."
                           (list (cons #\0 ',accessor-name)
                                 (cons #\1 ',var)))
                          ,var)))
              (,accessor-name (i ,var)
                              (declare (xargs :guard
                                              (and (,top-recog ,var)
                                                   (integerp i)
                                                   (<= 0 i)
                                                   (< i (,length-name ,var)))
                                              :verify-guards t))
                              (nth i (nth ,n ,var)))
              (,updater-name (i v ,var)
                             (declare (xargs :guard
                                             (and (,top-recog ,var)
                                                  (integerp i)
                                                  (<= 0 i)
                                                  (< i (,length-name ,var))
                                                  ,@(if (eq array-etype-term
                                                            t)
                                                        nil
                                                      (list array-etype-term)))
                                             :verify-guards t))
                             (update-nth-array ,n i v ,var)))
           (defstobj-field-fns-axiomatic-defs
             top-recog var (+ n 1) (cdr field-templates) wrld)))
;---<
         (hashp
          (append
           `((,accessor-name
              (k ,var)
              (declare (xargs :guard ,(if (eq hash-test 'eql)
                                          `(and (,top-recog ,var)
                                                (eqlablep k))
                                        `(,top-recog ,var))
                              :verify-guards t))
              (cdr (hons-assoc-equal k (nth ,n ,var))))
             (,updater-name
              (k v ,var)
              (declare (xargs :guard ,(if (eq hash-test 'eql)
                                          `(and (,top-recog ,var)
                                                (eqlablep k))
                                        `(,top-recog ,var))
                              :verify-guards t))
              (update-nth ,n (cons (cons k v) (nth ,n ,var)) ,var))
             (,boundp-name
              (k ,var)
              (declare (xargs :guard ,(if (eq hash-test 'eql)
                                          `(and (,top-recog ,var)
                                                (eqlablep k))
                                        `(,top-recog ,var))
                              :verify-guards t))
              (consp (hons-assoc-equal k (nth ,n ,var))))
             (,accessor?-name
              
              (k ,var)
              (declare (xargs :guard ,(if (eq hash-test 'eql)
                                          `(and (,top-recog ,var)
                                                (eqlablep k))
                                        `(,top-recog ,var))
                              :verify-guards t))
              (mv (,accessor-name k ,var)
                  (,boundp-name k ,var)))
             (,remove-name
              (k ,var)
              (declare (xargs :guard ,(if (eq hash-test 'eql)
                                          `(and (,top-recog ,var)
                                                (eqlablep k))
                                        `(,top-recog ,var))
                              :verify-guards t))
              (update-nth ,n (hons-remove-assoc k (nth ,n ,var)) ,var))
             (,count-name
              (,var)
              (declare (xargs :guard (,top-recog ,var)))
              (count-keys (nth ,n ,var)))
             (,clear-name
              (,var)
              (declare (xargs :guard (,top-recog ,var)))
              (update-nth ,n nil ,var))
             (,init-name
              (size rehash-size rehash-threshold ,var)
              (declare (xargs :guard (and (,top-recog ,var)
                                          (or (natp size)
                                              (not size))
                                          (or (and (rationalp rehash-size)
                                                   (< 1 rehash-size))
                                              (not rehash-size))
                                          (or (and (rationalp rehash-threshold)
                                                   (<= 0 rehash-threshold)
                                                   (<= rehash-threshold 1))
                                              (not rehash-threshold))))
                       (ignorable size rehash-size rehash-threshold))
              (update-nth ,n nil ,var)))
           (defstobj-field-fns-axiomatic-defs
             top-recog var (+ n 1) (cdr field-templates) wrld)))
;   >---
         (t
          (append
           `((,accessor-name (,var)
                             (declare (xargs :guard (,top-recog ,var)
                                             :verify-guards t))
                             (nth ,n ,var))
             (,updater-name (v ,var)
                            (declare (xargs :guard
                                            ,(if (eq type-term t)
                                                 `(,top-recog ,var)
                                               `(and ,type-term
                                                     (,top-recog ,var)))
                                            :verify-guards t))
                            (update-nth ,n v ,var)))
           (defstobj-field-fns-axiomatic-defs
             top-recog var (+ n 1) (cdr field-templates) wrld))))))))

(defun defstobj-axiomatic-init-fields (field-templates wrld)

; Keep this in sync with defstobj-raw-init-fields.

  (cond
   ((endp field-templates) nil)
   (t (let* ((field-template (car field-templates))
             (type (access defstobj-field-template
                           field-template
                           :type))
             (arrayp (and (consp type) (eq (car type) 'array)))
             (array-size (and arrayp (car (caddr type))))
;---<
             (hashp (and (consp type) (eq (car type) 'hash-table)))
;   >---
             (init0 (access defstobj-field-template
                            field-template
                            :init))
             (creator (get-stobj-creator (if arrayp (cadr type) type)
                                         wrld))
             (init (if creator
                       `(non-exec (,creator))
                     (kwote init0))))
        (cond
         (arrayp
          (cons `(make-list ,array-size :initial-element ,init)
                (defstobj-axiomatic-init-fields (cdr field-templates) wrld)))
;---<
         (hashp
          (cons nil
                (defstobj-axiomatic-init-fields (cdr field-templates) wrld)))
;   >---
         (t ; whether the type is given or not is irrelevant
          (cons init
                (defstobj-axiomatic-init-fields
                  (cdr field-templates) wrld))))))))

(defun defstobj-field-fns-raw-defs (var flush-var inline n field-templates)

; Warning: Keep the formals in the definitions below in sync with corresponding
; formals defstobj-field-fns-raw-defs.  Otherwise trace$ may not work
; correctly; we saw such a problem in Version_5.0 for a resize function.

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

  #-hons (declare (ignorable flush-var)) ; irrelevant var without hons
  (cond
   ((endp field-templates) nil)
   (t
    (append
     (let* ((field-template (car field-templates))
            (type (access defstobj-field-template field-template :type))
            (init (access defstobj-field-template field-template :init))
            (arrayp (and (consp type) (eq (car type) 'array)))
            (array-etype0 (and arrayp (cadr type)))
            (stobj-creator (get-stobj-creator (if arrayp array-etype0 type)
                                              nil))
            (scalar-type
             (if stobj-creator t type)) ; only used when (not arrayp)
            (array-etype (and arrayp
                              (if stobj-creator

; Stobj-creator is non-nil when array-etype is a stobj.  The real element type,
; then, is simple-array rather than a simple-array-type, so we might say that
; the parent stobj array is not simple.  But we will assume that the advantage
; of having a simple-vector for the parent stobj outweighs the advantage of
; having a simple-vector element type declaration.

                                  t
                                array-etype0)))
            (simple-type (and arrayp
                              (simple-array-type array-etype (caddr type))))
            (array-length (and arrayp (car (caddr type))))
            (vref (and arrayp
                       (if (eq (car simple-type) 'simple-vector)
                           'svref
                         'aref)))
            (fix-vref (and arrayp
                           (if (array-etype-is-fixnum-type array-etype)
                               'fix-aref
                             vref)))
            (accessor-name (access defstobj-field-template
                                   field-template
                                   :accessor-name))
            (updater-name (access defstobj-field-template
                                  field-template
                                  :updater-name))
            (length-name (access defstobj-field-template
                                 field-template
                                 :length-name))
            (resize-name (access defstobj-field-template
                                 field-template
                                 :resize-name))
            (resizable (access defstobj-field-template
                               field-template
                               :resizable))
;---<
            (hashp (and (consp type) (eq (car type) 'hash-table)))
            (hash-test (and hashp (cadr type)))
            (other (access defstobj-field-template
                           field-template
                           :other))
            (boundp-name (nth 0 other))
            (accessor?-name (nth 1 other))
            (remove-name (nth 2 other))
            (count-name (nth 3 other))
            (clear-name (nth 4 other))
            (init-name (nth 5 other))
;   >---
            )
       (cond
;---<
        (hashp
         `((,accessor-name
            (k ,var)
            ,@(and inline (list *stobj-inline-declare*))
            (values (gethash ,(if (eq hash-test 'hons-equal)
                                 `(hons-copy k)
                               'k)
                            (the hash-table (svref ,var ,n)))))
           (,updater-name
            (k v ,var)
            ,@(and inline (list *stobj-inline-declare*))
            (progn
              #+hons (memoize-flush ,var)
              (setf (gethash ,(if (eq hash-test 'hons-equal)
                                  `(hons-copy k)
                                'k)
                             (the hash-table (svref ,var ,n)))
                    v)
              ,var))
           (,boundp-name
            (k ,var)
            ,@(and inline (list *stobj-inline-declare*))
            (multiple-value-bind (val boundp)
                (gethash ,(if (eq hash-test 'hons-equal)
                              `(hons-copy k)
                            'k)
                         (the hash-table (svref ,var ,n)))
              (declare (ignore val))
              (if boundp t nil)))
           (,accessor?-name
            (k ,var)
            ,@(and inline (list *stobj-inline-declare*))
            (multiple-value-bind
                (val boundp)
                (gethash ,(if (eq hash-test 'hons-equal)
                              `(hons-copy k)
                            'k)
                         (the hash-table (svref ,var ,n)))
              (mv val (if boundp t nil))))
           (,remove-name
            (k ,var)
            ,@(and inline (list *stobj-inline-declare*))
            (progn
              #+(and hons (not acl2-loop-only))
              (memoize-flush ,var)
              (remhash ,(if (eq hash-test 'hons-equal)
                            `(hons-copy k)
                          'k)
                       (the hash-table (svref ,var ,n)))
              ,var))
           (,count-name
            (,var)
            ,@(and inline (list *stobj-inline-declare*))
            (hash-table-count (svref ,var ,n)))
           (,clear-name
            (,var)
            ,@(and inline (list *stobj-inline-declare*))
            (progn
              #+(and hons (not acl2-loop-only))
              (memoize-flush ,var)
              (clrhash (svref ,var ,n))
              ,var))
           (,init-name
            (size rehash-size rehash-threshold ,var)
            ,@(and inline (list *stobj-inline-declare*))
            (progn
              #+(and hons (not acl2-loop-only))
              (memoize-flush ,var)
              (setf (svref ,var ,n)
                    (make-hash-table
                     :test ',(case hash-test
                               (eql 'eql)
                               (equal 'equal)
                               (t (er hard hash-test
                                      "The hash test should be either EQL or ~
                                       EQUAL.~%")))
                     :size (or size 60)
                     :rehash-size (if rehash-size
                                      (float rehash-size)
                                    (float 17/10))
                     :rehash-threshold (if rehash-threshold
                                           (float rehash-threshold)
                                         (float 3/4))))
              ,var))))
;   >---
        (arrayp
         `((,length-name
            (,var)
            ,@(and inline (list *stobj-inline-declare*))
            ,@(if (not resizable)
                  `((declare (ignore ,var))
                    ,array-length)
                `((the (and fixnum (integer 0 *))
                       (length (svref ,var ,n))))))
           (,resize-name
            (i ,var)
            ,@(if (not resizable)
                  `((declare (ignore i))
                    (prog2$
                     (er hard ',resize-name
                         "The array field corresponding to accessor ~x0 of ~
                          stobj ~x1 was not declared :resizable t.  ~
                          Therefore, it is illegal to resize this array."
                         ',accessor-name
                         ',var)
                     ,var))
                `((if (not (and (integerp i)
                                (>= i 0)
                                (< i array-dimension-limit)))
                      (hard-error
                       ',resize-name
                       "Attempted array resize failed because the requested ~
                        size ~x0 was not a nonnegative integer less than the ~
                        value of Common Lisp constant array-dimension-limit, ~
                        which is ~x1.  These bounds on array sizes are fixed ~
                        by ACL2."
                       (list (cons #\0 i)
                             (cons #\1 array-dimension-limit)))
                    (let* ((var ,var)
                           (old (svref var ,n))
                           (min-index (min i (length old)))
                           (new (make-array$ i

; The :initial-element below is probably not necessary in the case
; that we are downsizing the array.  At least, CLtL2 does not make any
; requirements about specifying an :initial-element, even when an
; :element-type is supplied.  However, it seems harmless enough to go
; ahead and specify :initial-element even for downsizing: resizing is
; not expected to be fast, we save a case split here (at the expense
; of this comment!), and besides, we are protecting against the
; possibility that some Common Lisp will fail to respect the spec and
; will cause an error by trying to initialize a fixnum array (say)
; with NILs.

                                             :initial-element
                                             ',init
                                             :element-type
                                             ',array-etype)))
                      #+hons (memoize-flush ,flush-var)
                      (setf (svref var ,n)
                            (,(pack2 'stobj-copy-array- fix-vref)
                             old new 0 min-index))
                      ,@(and stobj-creator
                             `((when (< (length old) i)
                                 (loop for j from (length old) to (1- i)
                                       do (setf (svref new j)
                                                (,stobj-creator))))))
                      var)))))
           (,accessor-name
            (i ,var)
            (declare (type (and fixnum (integer 0 *)) i))
            ,@(and inline (list *stobj-inline-declare*))
            (the ,array-etype
                 (,vref (the ,simple-type (svref ,var ,n))
                        (the (and fixnum (integer 0 *)) i))))
           (,updater-name
            (i v ,var)
            (declare (type (and fixnum (integer 0 *)) i)
                     (type ,array-etype v))
            ,@(and inline (list *stobj-inline-declare*))
            (progn
              #+hons (memoize-flush ,flush-var)

; See the long comment below for the updater in the scalar case, about
; supporting *1* functions.

              (setf (,vref (the ,simple-type (svref ,var ,n))
                           (the (and fixnum (integer 0 *)) i))
                    (the ,array-etype v))
              ,var))))
        ((eq scalar-type t)
         `((,accessor-name (,var)
                           ,@(and inline (list *stobj-inline-declare*))
                           (svref ,var ,n))
           (,updater-name (v ,var)
                          ,@(and inline (list *stobj-inline-declare*))
                          (progn
                            #+hons (memoize-flush ,flush-var)

; For the case of a stobj field, we considered causing an error here since the
; raw Lisp code for stobj-let avoids calling updaters because there is no need:
; updates for fields that are stobjs have already updated destructively.
; However, a raw Lisp updater can be called by a *1* function, say *1*f,
; applied to live stobjs, when guard checking does not pass control to the raw
; Lisp function, f.  Perhaps we could optimize to avoid this, but there is no
; need; this setf is fast and is only called on behalf of executing *1*
; function calls.  See the comment referencing "defstobj-field-fns-raw-defs" in
; community book misc/nested-stobj-tests.lisp.  To see this point in action,
; evaluate the forms under that comment after modifying this definition by
; uncommenting the following line of code.

;                           ,@(when stobj-creator '((break$))) ; see just above

                            (setf (svref ,var ,n) v)
                            ,var))))
        (t
         (assert$
          (not stobj-creator) ; scalar-type is t for stobj-creator
          `((,accessor-name (,var)
                            ,@(and inline (list *stobj-inline-declare*))
                            (the ,scalar-type
                                 (aref (the (simple-array ,scalar-type (1))
                                            (svref ,var ,n))
                                       0)))
            (,updater-name (v ,var)
                           (declare (type ,scalar-type v))
                           ,@(and inline (list *stobj-inline-declare*))
                           (progn
                             #+hons (memoize-flush ,flush-var)
                             (setf (aref (the (simple-array ,scalar-type (1))
                                              (svref ,var ,n))
                                         0)
                                   (the ,scalar-type v))
                             ,var)))))))
     (defstobj-field-fns-raw-defs
       var flush-var inline (1+ n) (cdr field-templates))))))


(defun chk-stobj-field-descriptor (name field-descriptor non-memoizable
                                        ctx wrld state)

; See the comment just before chk-acceptable-defstobj1 for an explanation of
; our handling of Common Lisp compliance.

; The argument, non-memoizable, is the value of the :non-memoizable keyword of
; the defstobj event intrducing name.  Let us consider whether there is a need
; to add a check about :non-memoizable for the case of a stobj with stobj
; fields.

; On the one hand, it is fine for the parent stobj to be memoizable regardless
; of whether any child stobjs are non-memoizable.  Suppose that some child
; stobj is non-memoizable but the (new) parent stobj is memoizable.  The
; concern is the case that some memoized function reads the parent twice on the
; same inputs when between those reads, some child stobj has changed without
; any flushing of memoization tables (because the child stobj is
; non-memoizable).  But the only way to change a child stobj is by way of
; stobj-let, which flushes the memo table for each function that takes the
; parent stobj as an argument (since the parent is memoizable).

; On the other hand, suppose that some child stobj is memoizable but the (new)
; parent stobj is non-memoizable.  In this case, stobj-let does not flush the
; parent stobj's memo tables, and we return to the soundness bug illustrated in
; a comment in stobj-let-fn-raw.

  (cond
   ((symbolp field-descriptor) (value nil))
   (t
    (er-progn
     (cond ((and (consp field-descriptor)
                 (symbolp (car field-descriptor))
                 (keyword-value-listp (cdr field-descriptor))
                 (member-equal (length field-descriptor) '(1 3 5 7))
                 (let ((keys (odds field-descriptor)))
                   (and (no-duplicatesp keys)
                        (subsetp-eq keys '(:type :initially :resizable)))))
            (value nil))
           (t (er soft ctx
                  "The field descriptors of a single-threaded object ~
                   definition must be a symbolic field-name or a list of the ~
                   form (field-name :type type :initially val), where ~
                   field-name is a symbol.  The :type and :initially keyword ~
                   assignments are optional and their order is irrelevant.  ~
                   The purported descriptor ~x0 for a field in ~x1 is not of ~
                   this form."
                  field-descriptor
                  name)))
     (let* ((field (car field-descriptor))
            (type (if (assoc-keyword :type (cdr field-descriptor))
                      (cadr (assoc-keyword :type (cdr field-descriptor)))
                    t))
            (initp (assoc-keyword :initially (cdr field-descriptor)))
            (init (if initp (cadr initp) nil))
            (resizable (if (assoc-keyword :resizable (cdr field-descriptor))
                           (cadr (assoc-keyword :resizable
                                                (cdr field-descriptor)))
                         nil))
            (child-stobj-memoizable-error-string
             "It is illegal to declare stobj ~x0 as :NON-MEMOIZABLE, because ~
              it has a child stobj, ~x1, that was not thus declared.  See ~
              :DOC defstobj."))
       (cond
        ((and resizable (not (eq resizable t)))
         (er soft ctx
             "The :resizable value in the ~x0 field of ~x1 is illegal:  ~x2.  ~
              The legal values are t and nil."
             field name resizable))
        ((and (consp type)
              (eq (car type) 'array))
         (cond
          ((not (and (true-listp type)
                     (equal (length type) 3)
                     (true-listp (caddr type))
                     (equal (length (caddr type)) 1)))
           (er soft ctx
               "When a field descriptor specifies an ARRAY :type, the type ~
                must be of the form (ARRAY etype (n)).  Note that we only ~
                support single-dimensional arrays.  The purported ARRAY :type ~
                ~x0 for the ~x1 field of ~x2 is not of this form."
               type field name))
          (t (let* ((type0 (fix-stobj-array-type type wrld))
                    (etype (cadr type0))
                    (stobjp (stobjp etype t wrld))
                    (etype-term ; used only when (not stobjp)
                     (and (not stobjp) ; optimization
                          (translate-declaration-to-guard etype 'x wrld)))
                    (n (car (caddr type0)))
                    (etype-error-string
                     "The element type specified for the ~x0 field of ~x1, ~
                      namely ~x2, is not recognized by ACL2 as a type-spec ~
                      (see :DOC type-spec) or as a user-defined stobj name."))
               (cond
                ((not (natp n))
                 (er soft ctx
                     "An array dimension must be a non-negative integer or a ~
                      defined constant whose value is a non-negative integer. ~
                      ~ The :type ~x0 for the ~x1 field of ~x2 is thus ~
                      illegal."
                     type0 field name))
                (stobjp

; Defstobj-raw-init-fields depends on this check.  Also see the comment above
; explaining how stobj-let depends on this check.

                 (cond ((eq etype 'state)
                        (er soft ctx
                            etype-error-string
                            field name etype))
                       ((and non-memoizable
                             (not (getprop etype 'non-memoizable nil
                                           'current-acl2-world wrld)))
                        (er soft ctx
                            child-stobj-memoizable-error-string
                            name etype))
                       ((null initp) (value nil))
                       (t (er soft ctx
                              "The :initially keyword must be omitted for a ~
                               :type specified as an array of stobjs.  But ~
                               for :type ~x0, :initially is specified as ~x1 ~
                               for the ~x2 field of ~x3."
                              type init field name))))
                ((null etype-term)
                 (er soft ctx
                     etype-error-string
                     field name etype))
                (t
                 (er-let*
                     ((pair (simple-translate-and-eval etype-term
                                                       (list (cons 'x init))
                                                       nil
                                                       (msg
                                                        "The type ~x0"
                                                        etype-term)
                                                       ctx
                                                       wrld
                                                       state
                                                       nil)))

; pair is (tterm . val), where tterm is a term and val is its value
; under x<-init.

                   (er-progn
                    (chk-common-lisp-compliant-subfunctions
                     nil (list field) (list (car pair))
                     wrld "auxiliary function" ctx state)
                    (chk-unrestricted-guards-for-user-fns
                     (all-fnnames (car pair))
                     wrld ctx state)
                    (cond
                     ((not (cdr pair))
                      (er soft ctx
                          "The value specified by the :initially ~
                           keyword, namely ~x0, fails to satisfy the ~
                           declared type ~x1 in the array ~
                           specification for the ~x2 field of ~x3."
                          init etype field name))
                     (t (value nil)))))))))))
        ((assoc-keyword :resizable (cdr field-descriptor))
         (er soft ctx
             "The :resizable keyword is only legal for array types, hence is ~
              illegal for the ~x0 field of ~x1."
             field name))
;---<
        ((and (consp type)
              (eq (car type) 'hash-table))
         (cond ((or (atom (cdr type))
                    (not (member (cadr type)
                                 '(EQL 
                                   EQUAL
                                   #+(and hons (not acl2-loop-only))
                                   HONS-EQUAL))))
                (er soft ctx
                    "A hash-table type must be specified as (HASH-TABLE ~
                     TEST), where test is EQL, EQUAL, or (when built with the ~
                     HONS extension) HONS-EQUAL.  The test given was ~x0.~%"
                    (and (consp (cdr type))
                         (cadr type))))
               (t (value nil))))
;   >---
        (t (let* ((stobjp (stobjp type t wrld))
                  (type-term ; used only when (not stobjp)
                   (and (not stobjp) ; optimization
                        (translate-declaration-to-guard type 'x wrld)))
                  (type-error-string
                   "The :type specified for the ~x0 field of ~x1, namely ~x2, ~
                    is not recognized by ACL2 as a type-spec (see :DOC ~
                    type-spec) or as a user-defined stobj name."))
             (cond
              (stobjp

; Defstobj-raw-init-fields depends on this check.  Also see the comment above
; explaining how stobj-let depends on this check.

               (cond ((eq type 'state)
                      (er soft ctx
                          type-error-string
                          field name type))
                     ((and non-memoizable
                           (not (getprop type 'non-memoizable nil
                                         'current-acl2-world wrld)))
                      (er soft ctx
                          child-stobj-memoizable-error-string
                          name type))
                     ((null initp) (value nil))
                     (t (er soft ctx
                            "The :initially keyword must be omitted for a ~
                             :type specified as a stobj.  But for :type ~x0, ~
                             :initially is specified as ~x1 for the ~x2 field ~
                             of ~x3."
                            type init field name))))
              ((null type-term)
               (er soft ctx
                   type-error-string
                   field name type))
              (t
               (er-let* ((pair (simple-translate-and-eval type-term
                                                          (list (cons 'x init))
                                                          nil
                                                          (msg
                                                           "The type ~x0"
                                                           type-term)
                                                          ctx
                                                          wrld
                                                          state
                                                          nil)))

; pair is (tterm . val), where tterm is a term and val is its value
; under x<-init.

                 (er-progn
                  (chk-common-lisp-compliant-subfunctions
                   nil (list field) (list (car pair))
                   wrld "body" ctx state)
                  (chk-unrestricted-guards-for-user-fns
                   (all-fnnames (car pair))
                   wrld ctx state)
                  (cond
                   ((not (cdr pair))
                    (er soft ctx
                        "The value specified by the :initially keyword, ~
                         namely ~x0, fails to satisfy the declared :type ~x1 ~
                         for the ~x2 field of ~x3."
                        init type field name))
                   (t (value nil)))))))))))))))

(defun chk-acceptable-defstobj1 (name field-descriptors ftemps renaming
                                      non-memoizable ctx wrld state names
                                      const-names)

; We check whether it is legal to define name as a single-threaded
; object with the description given in field-descriptors.  We know
; name is a legal (and new) stobj name and we know that renaming is a
; symbol to symbol doublet-style alist.  But we know nothing else.  We
; either signal an error or return the world in which the event is to
; be processed (thus implementing redefinitions).  Names is, in
; general, the actual set of names that the defstobj event will
; introduce.  That is, it contains the images of the default names
; under the renaming alist.  We accumulate the actual names into it as
; we go and check that it contains no duplicates at the termination of
; this function.  All of the names in names are to be defined as
; functions with :VERIFY-GUARDS T.  See the comment above about
; Common Lisp compliance.

  (cond
   ((endp ftemps)
    (let* ((recog-name (defstobj-fnname name :recognizer :top renaming))
           (creator-name (defstobj-fnname name :creator :top renaming))
           (names (list* recog-name creator-name names)))
      (er-progn
       (chk-all-but-new-name recog-name ctx 'function wrld state)
       (chk-all-but-new-name creator-name ctx 'function wrld state)
       (chk-acceptable-defstobj-renaming name field-descriptors renaming
                                         ctx state nil)

; Note: We insist that all the names be new.  In addition to the
; obvious necessity for something like this, we note that this does
; not permit us to have redundantly defined any of these names.  For
; example, the user might have already defined a field recognizer,
; PCP, that is identically defined to what we will lay down.  But we
; do not allow that.  We basically insist that we have control over
; every one of these names.

       (chk-just-new-names names 'function nil ctx wrld state)
       (chk-just-new-names const-names 'const nil ctx wrld state))))
   (t

; An element of field-descriptors (i.e., of ftemps) is either a symbolic field
; name, field, or else of the form (field :type type :initially val), where
; either or both of the keyword fields can be omitted.  Val must be an evg,
; i.e., an unquoted constant like t, nil, 0 or undef (the latter meaning the
; symbol 'undef).  :Type defaults to the unrestricted type t and :initially
; defaults to nil.  Type is either a primitive type, as recognized by
; translate-declaration-to-guard, or a stobj name, or else is of the form
; (array ptype (n)), where ptype is a primitive type or stobj name and n is an
; positive integer constant.  If type is a stobj name or an array of such, then
; :initially must be omitted.

    (er-progn
     (chk-stobj-field-descriptor name (car ftemps) non-memoizable ctx wrld
                                 state)
     (let* ((field (if (atom (car ftemps))
                       (car ftemps)
                     (car (car ftemps))))
            (type (if (consp (car ftemps))
                      (or (cadr (assoc-keyword :type
                                               (cdr (car ftemps))))
                          t)
                    t))
;---<
            (key2 (if (consp type)
                     (case (car type)
                       (array :array)
                       (hash-table :hash-table)
                       (t :non-array))
                    :non-array))
            (boundp-name (defstobj-fnname field :boundp key2 renaming))
            (accessor?-name (defstobj-fnname field :accessor? key2
                              renaming))
            (remove-name (defstobj-fnname field :remove key2
                           renaming))
            (count-name (defstobj-fnname field :count key2 renaming))
            (clear-name (defstobj-fnname field :clear key2 renaming))
            (init-name (defstobj-fnname field :init key2 renaming))
;   >---
            (fieldp-name (defstobj-fnname field :recognizer key2 renaming))
            (accessor-name (defstobj-fnname field :accessor key2 renaming))
            (accessor-const-name (defconst-name accessor-name))
            (updater-name (defstobj-fnname field :updater key2 renaming))
            (length-name (defstobj-fnname field :length key2 renaming))
            (resize-name (defstobj-fnname field :resize key2 renaming)))
       (er-progn
        (chk-all-but-new-name fieldp-name ctx 'function wrld state)
        (chk-all-but-new-name accessor-name ctx 'function wrld state)
        (chk-all-but-new-name updater-name ctx 'function wrld state)
        (chk-all-but-new-name accessor-const-name ctx 'const wrld state)
        (if (eq key2 :array)
            (er-progn (chk-all-but-new-name length-name ctx 'function wrld state)
                      (chk-all-but-new-name resize-name ctx 'function wrld state))
;---<
          (if (eq key2 :hash-table)
              (er-progn (chk-all-but-new-name boundp-name ctx
                                              'function wrld state)
                        (chk-all-but-new-name accessor?-name ctx
                                              'function wrld state)
                        (chk-all-but-new-name remove-name ctx
                                              'function wrld state))
            (value nil)
;   >---
            ))
        (chk-acceptable-defstobj1 name field-descriptors (cdr ftemps)
                                  renaming non-memoizable ctx wrld state
                                  (list* fieldp-name
                                         accessor-name
                                         updater-name
                                         (if (eq key2 :array)
                                             (list* length-name
                                                    resize-name
                                                    names)
;---<
                                           (if (eq key2 :hash-table)
                                               (list* boundp-name
                                                      accessor?-name
                                                      remove-name
                                                      count-name
                                                      clear-name
                                                      init-name
                                                      names)
                                             names)
;   >---
                                           ))
                                  (cons accessor-const-name
                                        const-names))))))))


(defun put-stobjs-in-and-outs1 (name field-templates wrld)

; See put-stobjs-in-and-outs for a table that explains what we're doing.

  (cond
   ((endp field-templates) wrld)
   (t (let* ((field-template (car field-templates))
             (type (access defstobj-field-template field-template
                           :type))
             (acc-fn (access defstobj-field-template field-template
                             :accessor-name))
             (upd-fn (access defstobj-field-template field-template
                             :updater-name))
             (length-fn (access defstobj-field-template field-template
                                :length-name))
             (resize-fn (access defstobj-field-template field-template
                                :resize-name))
             ;;---<
             (other (access defstobj-field-template
                            field-template
                            :other))
             (boundp-fn (nth 0 other))
             (accessor?-fn (nth 1 other))
             (remove-fn (nth 2 other))
             (count-fn (nth 3 other))
             (clear-fn (nth 4 other))
             (init-fn (nth 5 other))
             ;;   >---
             )
        (put-stobjs-in-and-outs1
         name
         (cdr field-templates)
         (cond
          ((and (consp type)
                (eq (car type) 'array))
           (let* ((etype (cadr type))
                  (stobj-flg (and (stobjp etype t wrld)
                                  etype)))
             (putprop
              length-fn 'stobjs-in (list name)
              (putprop
               resize-fn 'stobjs-in (list nil name)
               (putprop
                resize-fn 'stobjs-out (list name)
                (putprop
                 acc-fn 'stobjs-in (list nil name)
                 (putprop-unless
                  acc-fn 'stobjs-out (list stobj-flg) '(nil)
                  (putprop
                   upd-fn 'stobjs-in (list nil stobj-flg name)
                   (putprop
                    upd-fn 'stobjs-out (list name) wrld)))))))))
;;---<
          ((and (consp type)
                (eq (car type) 'hash-table))
           (putprop
            init-fn 'stobjs-in (list nil nil nil name)
            (putprop
             init-fn 'stobjs-out (list name)
             (putprop
              clear-fn 'stobjs-in (list name)
              (putprop
               clear-fn 'stobjs-out (list name)
               (putprop
                count-fn 'stobjs-in (list name)
                (putprop
                 remove-fn 'stobjs-in (list nil name)
                 (putprop
                  remove-fn 'stobjs-out (list name)
                  (putprop
                   accessor?-fn 'stobjs-in (list nil name)
                   (putprop
                    boundp-fn 'stobjs-in (list nil name)
                    (putprop
                     acc-fn 'stobjs-in (list nil name)
                     (putprop
                      upd-fn 'stobjs-in (list nil nil name)
                      (putprop
                       upd-fn 'stobjs-out (list name) wrld)))))))))))))
;;   >---
          (t
           (let ((stobj-flg (and (stobjp type t wrld)
                                 type)))
             (putprop
              acc-fn 'stobjs-in (list name)
              (putprop-unless
               acc-fn 'stobjs-out (list stobj-flg) '(nil)
               (putprop
                upd-fn 'stobjs-in (list stobj-flg name)
                (putprop
                 upd-fn 'stobjs-out (list name) wrld))))))))))))

(redef-)


;; Macro for proving theorems like the ones above about a hash field:

(defmacro prove-ht-theorems (field stobj &optional renaming)
  (let ((get (defstobj-fnname field :accessor :hash-table renaming))
        (boundp (defstobj-fnname field :boundp :hash-table renaming))
        (put (defstobj-fnname field :updater :hash-table renaming))
        (rem (defstobj-fnname field :remove :hash-table renaming))
        (count (defstobj-fnname field :count :hash-table renaming))
        (clear (defstobj-fnname field :clear :hash-table renaming))
        (init (defstobj-fnname field :init :hash-table renaming))
        (make (defstobj-fnname stobj :creator :hash-table renaming)))
    `(progn
       (defthm ,(packn-pos (list field "-INIT-IS-CLEAR") field)
         (equal (,init size rehash-size rehash-threshold ,stobj)
                (,clear ,stobj)))

       (defthm ,(packn-pos (list field "-GET-BOUNDP") field)
         (implies (,get k ,stobj)
                  (,boundp k ,stobj)))

       (defthm ,(packn-pos (list field "-BOUNDP-START") field)
         (not (,boundp k (,make))))

       (defthm ,(packn-pos (list field "-BOUNDP-CLEAR") field)
         (not (,boundp k (,clear ,stobj))))

       (defthm ,(packn-pos (list field "-BOUNDP-PUT-SAME") field)
         (,boundp k (,put k v ,stobj)))

       (defthm ,(packn-pos (list field "-BOUNDP-PUT-DIFF") field)
         (implies (not (equal j k))
                  (equal (,boundp k (,put j v ,stobj))
                         (,boundp k ,stobj))))

       (defthm ,(packn-pos (list field "-GET-PUT-SAME") field)
         (equal (,get k (,put k v ,stobj))
                v))

       (defthm ,(packn-pos (list field "-GET-PUT-DIFF") field)
         (implies (not (equal j k))
                  (equal (,get k (,put j v ,stobj))
                         (,get k ,stobj))))

       (defthm ,(packn-pos (list field "-REM-BOUNDP-SAME") field)
         (not (,boundp k (,rem k ,stobj))))

       (defthm ,(packn-pos (list field "-REM-BOUNDP-DIFF") field)
         (implies (not (equal j k))
                  (equal (,boundp k (,rem j ,stobj))
                         (,boundp k ,stobj))))

       (defthm ,(packn-pos (list field "-REM-GET-DIFF") field)
         (implies (not (equal j k))
                  (equal (,get k (,rem j ,stobj))
                         (,get k ,stobj))))

       (defthm ,(packn-pos (list field "-COUNT-START") field)
         (equal (,count (,make)) 0))

       (defthm ,(packn-pos (list field "-COUNT-PUT") field)
         (equal (,count (,put k v ,stobj))
                (if (,boundp k ,stobj)
                    (,count ,stobj)
                  (+ 1 (,count ,stobj)))))

       (defthm ,(packn-pos (list field "-COUNT-REM") field)
         (equal (,count (,rem k ,stobj))
                (if (,boundp k ,stobj)
                    (- (,count ,stobj) 1)
                  (,count ,stobj))))

       (defthm ,(packn-pos (list field "-COUNT-CLEAR") field)
         (equal (,count (,clear ,stobj))
                0)))))



(local
 (progn

   (defstobj bigstobj
     (bigarray :type (array (unsigned-byte 16) (100))
               :initially 0)
     (bighash :type (hash-table eql))
     (slowhash :type (hash-table equal))
     )

   (make-event
    (let* ((bigstobj (bighash-put 0 0 bigstobj))
           (bigstobj (slowhash-put (list 0) 0 bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (include-book "misc/assert" :dir :system)

   (assert! (equal (bighash-get 0 bigstobj) 0))
   (assert! (equal (slowhash-get '(0) bigstobj) 0))

   (defun init-stuff (n bigstobj state)
     (declare (xargs :stobjs (bigstobj state)
                     :verify-guards nil
                     :guard (natp n)))
     (if (zp n)
         (mv bigstobj state)
       (mv-let (rnd state) (random$ 10000 state)
         (let* ((bigstobj (update-bigarrayi n rnd bigstobj))
                (bigstobj (bighash-put n rnd bigstobj))
                (bigstobj (slowhash-put (list n) rnd bigstobj)))
           (init-stuff (- n 1) bigstobj state)))))

   (make-event
    (mv-let (bigstobj state)
      (init-stuff 99 bigstobj state)
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (equal (bighash-count bigstobj) 100))
   (assert! (equal (slowhash-count bigstobj) 100))

   (make-event
    (let* ((bigstobj (slowhash-put (cons 1 2) 3 bigstobj))
           (bigstobj (slowhash-put (cons 1 2) 4 bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (equal (slowhash-get (cons 1 2) bigstobj) 4))
   (assert! (equal (slowhash-count bigstobj) 101))

   

   (defun check-same (n bigstobj)
     (declare (xargs :stobjs (bigstobj)
                     :verify-guards nil
                     :guard (natp n)))
     (if (zp n)
         t
       (let ((expect (bigarrayi n bigstobj)))
         (and (equal (bighash-get n bigstobj) expect)
              (equal (slowhash-get (list n) bigstobj) expect)
              (equal (bighash-boundp n bigstobj) t)
              (equal (slowhash-boundp (list n) bigstobj) t)
              (equal (mv-list 2 (bighash-get? n bigstobj)) (list expect t))
              (equal (mv-list 2 (slowhash-get? (list n) bigstobj)) (list expect
                                                                         t))
              (check-same (- n 1) bigstobj)))))

   (assert! (check-same 99 bigstobj))

   (assert! (not (bighash-boundp 101 bigstobj)))
   (assert! (equal (mv-list 2 (bighash-get? 101 bigstobj)) (list nil nil)))

   (assert! (not (slowhash-boundp 101 bigstobj)))
   (assert! (equal (mv-list 2 (slowhash-get? 101 bigstobj)) (list nil nil)))

   (assert! (not (slowhash-boundp (list 101) bigstobj)))
   (assert! (equal (mv-list 2 (slowhash-get? (list 101) bigstobj)) (list nil nil)))

   (make-event
    (let* ((bigstobj (bighash-rem 3 bigstobj))
           (bigstobj (slowhash-rem (list 3) bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (not (bighash-boundp 3 bigstobj)))
   (assert! (not (slowhash-boundp (list 3) bigstobj)))

   (assert! (equal (slowhash-count bigstobj) 100))
   (assert! (equal (bighash-count bigstobj) 99))

   (make-event
    (let* ((bigstobj (slowhash-clear bigstobj))
           (bigstobj (bighash-init 10000 nil nil bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))   

   (assert! (equal (bighash-count bigstobj) 0))
   (assert! (equal (slowhash-count bigstobj) 0))
   (assert! (equal (bighash-get 5 bigstobj) nil))
   (assert! (equal (slowhash-get (list 5) bigstobj) nil))

   ))




