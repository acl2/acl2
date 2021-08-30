; Copyright (C) 2019 Centaur Technology
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


(include-book "std/util/da-base" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "updater-independence")

(program)

;; (std::def-primitive-aggregate nicestobj-field
;;   (name
;;    kwd-name
;;    type
;;    pred
;;    fix
;;    initially
;;    resizable
;;    arrayp
;;    hashp
;;    ;; function names
;;    access
;;    update
;;    resize
;;    length
;;    boundp
;;    access?
;;    remove
;;    count
;;    clear
;;    init
;; ))

(defconst *nicestobj-field-userkeys*
  '(:key :type :pred :fix :rule-classes :initially :resizable
    ;; function names
    :fieldname
    :access
    :base-access
    :update
    :base-update
    :resize
    :length
    :recognizer

    ;; only applicable to add-ons/hash-stobjs.lisp hash table fields
    :boundp
    :access?
    :remove
    :count
    :clear
    :init
    :elementp-of-nil))

(defconst *nicestobj-field-keys*
  (append '(:name :arrayp :hashp :elt-type :renaming :stobjp) *nicestobj-field-userkeys*))



(defun kwd-alist-field-accessor-alist (keys)
  (if (atom keys)
      nil
    (cons (cons (car keys)
                `(lambda (x) (cdr (assoc-eq ,(car keys) x))))
          (kwd-alist-field-accessor-alist (cdr keys)))))


(make-event
 (std::da-make-binder-gen
  'nicestobj-field
  (kwd-alist-field-accessor-alist *nicestobj-field-keys*)))

(defmacro kwd-alist-add-default (key val kwd-alist)
  `(if (assoc ,key ,kwd-alist)
       ,kwd-alist
    (cons (cons ,key ,val) ,kwd-alist)))
            
(defun member-eq-tree (x tree)
  (declare (xargs :guard (symbolp x)))
  (if (atom tree)
      (eq x tree)
    (or (member-eq-tree x (car tree))
        (member-eq-tree x (cdr tree)))))


(defun congruent-stobj-pred (x wrld)
  (b* ((stobj (or (fgetprop x 'acl2::congruent-stobj-rep nil wrld) x))
       (prop (fgetprop stobj 'acl2::stobj nil wrld)))
    (and prop
         (access acl2::stobj-property prop :recognizer))))

(defun remove-redundant-pairs (x)
  (if (atom x)
      nil
    (if (eq (caar x) (cdar x))
        (remove-redundant-pairs (cdr x))
      (cons (car x) (remove-redundant-pairs (cdr x))))))


(defun parse-nicestobj-field (stobjname field wrld)
  (b* ((std::__function__ 'parse-nicestobj-field)
       ((unless (and (consp field)
                     (symbolp (car field))
                     (keyword-value-listp (cdr field))))
        (raise "Malformed nicestobj field: ~x0~%" field))
       (name (car field))
       (args (cdr field))
       ((mv kwd-alist rest)
        (std::extract-keywords `(nicestobj-field ,name) *nicestobj-field-userkeys* args nil))
       ((when rest)
        (raise "Malformed nicestobj field: ~x0  Remaining after keyword extraction: ~x1~%" field rest))
       (kwd-alist (cons (cons :name name) kwd-alist))
       (kwd-alist (kwd-alist-add-default :type t kwd-alist))
       (type (cdr (assoc :type kwd-alist)))
       ((when (and (consp type) (member-eq (car type) '(acl2::hash-table))))
        (raise "Nicestobj doesn't support hash-table fields yet~%"))
       (arrayp (and (consp type)
                    (eq (car type) 'array)))
       (elt-type (if (and (consp type)
                           (member-eq (car type) '(array acl2::hash-table)))
                      (cadr type)
                    type))
       (type-pred (acl2::translate-declaration-to-guard elt-type name nil))
       ;; (typep (and type-pred (not (member-eq-tree 'satisfies type))))
       (stobj-pred (and (not type-pred)
                        (symbolp elt-type)
                        (congruent-stobj-pred elt-type wrld)))
       (type-pred-expr (or type-pred 
                           (and stobj-pred
                                `(,stobj-pred ,name))))
       (type-pred-fn (and type-pred-expr
                          ;; special case for when the type is T
                          (member-eq-tree name type-pred-expr)
                          `(lambda (,name) ,type-pred-expr)))
       (kwd-alist (cons (cons :elt-type elt-type) kwd-alist))
       (kwd-alist (cons (cons :stobjp stobj-pred) kwd-alist))
       (kwd-alist (cons (cons :arrayp arrayp) kwd-alist))
       (kwd-alist (kwd-alist-add-default :key (intern-in-package-of-symbol (symbol-name name) :foo) kwd-alist))
       (kwd-alist (kwd-alist-add-default :pred type-pred-fn kwd-alist))
       (kwd-alist (kwd-alist-add-default :rule-classes :rewrite kwd-alist))
       (kwd-alist (kwd-alist-add-default :fieldname
                                         (intern-in-package-of-symbol
                                          (concatenate 'string (symbol-name stobjname) "->"
                                                       (symbol-name name))
                                          stobjname)
                                         kwd-alist))
       (fieldname (cdr (assoc :fieldname kwd-alist)))
       (kwd-alist (kwd-alist-add-default :access
                                         (intern-in-package-of-symbol
                                          (concatenate 'string (symbol-name stobjname) "->"
                                                       (symbol-name name)
                                                       (if arrayp "I" ""))
                                          stobjname)
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :base-access
                                         (if (cdr (assoc :fix kwd-alist))
                                             (intern-in-package-of-symbol
                                              (concatenate 'string (symbol-name stobjname) "->"
                                                           (symbol-name name)
                                                           (if arrayp "I" "")
                                                           "^")
                                              stobjname)
                                           (cdr (assoc :access kwd-alist)))
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :update
                                         (intern-in-package-of-symbol
                                          (concatenate 'string "UPDATE-"
                                                       (symbol-name stobjname) "->"
                                                       (symbol-name name)
                                                       (if arrayp "I" ""))
                                          stobjname)
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :base-update
                                         (if (and (cdr (assoc :fix kwd-alist))
                                                  (not stobj-pred))
                                             (intern-in-package-of-symbol
                                              (concatenate 'string "UPDATE-"
                                                           (symbol-name stobjname) "->"
                                                           (symbol-name name)
                                                           (if arrayp "I" "")
                                                           "^")
                                              stobjname)
                                           (cdr (assoc :update kwd-alist)))
                                         kwd-alist))
       (kwd-alist (if arrayp
                      (kwd-alist-add-default :length
                                             (intern-in-package-of-symbol
                                              (concatenate 'string (symbol-name stobjname) "->"
                                                           (symbol-name name)
                                                           "-LENGTH")
                                              stobjname)
                                             kwd-alist)
                    kwd-alist))
       (kwd-alist (if arrayp
                      (kwd-alist-add-default :resize
                                             (intern-in-package-of-symbol
                                              (concatenate 'string
                                                           "RESIZE-"
                                                           (symbol-name stobjname) "->"
                                                           (symbol-name name))
                                              stobjname)
                                             kwd-alist)
                    kwd-alist))
       (kwd-alist (kwd-alist-add-default :recognizer
                                         (intern-in-package-of-symbol
                                          (concatenate 'string
                                                       (symbol-name stobjname) "->"
                                                       (symbol-name name) "P")
                                          stobjname)
                                         kwd-alist))
       (array-key (if arrayp :array :non-array))
       (kwd-alist (cons (cons :renaming
                              (remove-redundant-pairs
                               (append (and arrayp
                                            (list (cons (acl2::defstobj-fnname fieldname :length :array nil)
                                                        (cdr (assoc :length kwd-alist)))
                                                  (cons (acl2::defstobj-fnname fieldname :resize :array nil)
                                                        (cdr (assoc :resize kwd-alist)))))
                                       (list (cons (acl2::defstobj-fnname fieldname :accessor array-key nil)
                                                   (cdr (assoc :base-access kwd-alist)))
                                             (cons (acl2::defstobj-fnname fieldname :updater array-key nil)
                                                   (cdr (assoc :base-update kwd-alist)))
                                             (cons (acl2::defstobj-fnname fieldname :recognizer array-key nil)
                                                   (cdr (assoc :recognizer kwd-alist)))))))
                        kwd-alist)))
    kwd-alist))

(defun parse-nicestobj-fields (stobjname fields wrld)
  (if (atom fields)
      nil
    (cons (parse-nicestobj-field stobjname (car fields) wrld)
          (parse-nicestobj-fields stobjname (cdr fields) wrld))))


(defun nicestobj-field-template (field stobjname lastp)
  (b* (((nicestobj-field field)))
    (acl2::make-tmplsubst
     :features (append (if field.fix '(:fix) '(:no-fix))
                       (if field.pred '(:pred) '(:no-pred))
                       ;; (if field.rename-update '(:rename-updater) '(:no-rename-updater))
                       (if field.stobjp '(:stobjp) '(:not-stobjp))
                       (if field.arrayp '(:arrayp) '(:not-arrayp))
                       (if field.resizable '(:resizable) '(:not-resizable))
                       (if field.elementp-of-nil '(:elementp-of-nil) '(:not-elementp-of-nil)))
     :atoms `((<field> . ,field.name)
              (<fieldname> . ,field.fieldname)
              (<stobjname> . ,stobjname)
              (:<field> . ,field.key)
              (:<fieldcase> . ,(if lastp t field.key))
              (<type> . ,field.type)
              (<elt-type> . ,field.elt-type)
              (<initially> . ,field.initially)
              (<pred> . ,field.pred)
              (<fix> . ,field.fix)
              (<access> . ,field.access)
              (<update> . ,field.update)
              (<length> . ,field.length)
              (<resize> . ,field.resize)
              (<recognizer> . ,field.recognizer)
              (<base-access> . ,field.base-access)
              (<base-update> . ,field.base-update)
              (<rule-classes> . ,field.rule-classes)
              (<resizable> . ,field.resizable))
     :splices `((<renaming> . ,(pairlis$ (strip-cars field.renaming)
                                         (pairlis$ (strip-cdrs field.renaming) nil))))
     :strs `(("<FIELD>" . ,(symbol-name field.name))
             ("<FIELDNAME>" . ,(symbol-name field.fieldname))
             ("<ACCESS>" . ,(symbol-name field.access))
             ("<BASE-ACCESS>" . ,(symbol-name field.base-access))
             ("<UPDATE>" . ,(symbol-name field.update))
             ("<RECOGNIZER>" . ,(symbol-name field.recognizer))
             ,@(and field.arrayp
                    `(("<LENGTH>" . ,(symbol-name field.length))
                      ("<RESIZE>" . ,(symbol-name field.resize)))))
     :pkg-sym stobjname)))

(defun nicestobj-field-templates (fields stobjname)
  (if (atom fields)
      nil
    (cons (nicestobj-field-template (car fields) stobjname (atom (cdr fields)))
          (nicestobj-field-templates (cdr fields) stobjname))))



(defconst *nicestobj-userkeys*
  '(:inline
    :non-memoizable
    :fieldp
    :field-fix
    :field-equiv
    :get
    :pred))

(defconst *nicestobj-keys*
  (append '(:name :fields :raw-fields :template :rename-pred) *nicestobj-userkeys*))

(make-event
 (std::da-make-binder-gen
  'nicestobj
  (kwd-alist-field-accessor-alist *nicestobj-keys*)))


(defun parse-nicestobj (stobjname rest wrld)
  (b* ((std::__function__ 'parse-nicestobj)
       ((mv kwd-alist raw-fields)
        (std::extract-keywords `(nicestobj ,stobjname) *nicestobj-userkeys* rest nil))
       ((unless raw-fields)
        (raise "Nicestobj must have at least one field")) 
       (fields (parse-nicestobj-fields stobjname raw-fields wrld))
       (field-templates (nicestobj-field-templates fields stobjname))
       (kwd-alist (kwd-alist-add-default :inline t kwd-alist))
       (kwd-alist (kwd-alist-add-default :non-memoizable nil kwd-alist))
       (default-pred ;; from defstobj-fnname
         (acl2::packn-pos (list stobjname "P") stobjname))
       (kwd-alist (kwd-alist-add-default :pred default-pred kwd-alist))
       (kwd-alist (kwd-alist-add-default :rename-pred
                                         (not (eq (cdr (assoc :pred kwd-alist)) default-pred))
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :fieldp
                                         (intern-in-package-of-symbol
                                          (concatenate 'string (symbol-name stobjname) "-FIELD-P")
                                          stobjname)
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :field-fix
                                         (let ((fieldp (cdr (assoc :fieldp kwd-alist))))
                                           (intern-in-package-of-symbol
                                            (concatenate 'string (symbol-name (std::strip-p-from-symbol fieldp))
                                                         "-FIX")
                                            fieldp))
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :field-equiv
                                         (let ((fieldp (cdr (assoc :fieldp kwd-alist))))
                                           (intern-in-package-of-symbol
                                            (concatenate 'string (symbol-name (std::strip-p-from-symbol fieldp))
                                                         "-EQUIV")
                                            fieldp))
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :get
                                         (intern-in-package-of-symbol
                                          (concatenate 'string (symbol-name stobjname) "-GET")
                                          stobjname)
                                         kwd-alist))
       ((nicestobj x) kwd-alist)
       (template1 (acl2::make-tmplsubst
                   :atoms `((<stobjname> . ,stobjname)
                            (<inline> . ,x.inline)
                            (<non-memoizable> . ,x.non-memoizable)
                            (<fieldp> . ,x.fieldp)
                            (<get> . ,x.get)
                            (<field-fix> . ,x.field-fix)
                            (<field-equiv> . ,x.field-equiv)
                            (<stobjpred> . ,x.pred))
                   :strs `(("<STOBJNAME>" . ,(symbol-name stobjname))
                           ("<STOBJPRED>" . ,(symbol-name x.pred)))
                   :features (if x.rename-pred '(:rename-pred) '(:no-rename-pred))
                   :pkg-sym stobjname))
       (field-templates (acl2::combine-each-tmplsubst-with-default field-templates template1))
       (template (acl2::change-tmplsubst template1
                                         :subsubsts `((:fields . ,field-templates))))
       
       (kwd-alist (list* (cons :name stobjname)
                         (cons :fields fields)
                         (cons :raw-fields raw-fields)
                         (cons :template template)
                         kwd-alist)))
    kwd-alist))

(defconst *nicestobj-template*
  '(progn
     (defstobj <stobjname>
       (:@proj :fields
        (<fieldname> :type <type>
                     (:@ :not-stobjp :initially <initially>)
                     (:@ :arrayp :resizable <resizable>)))
       :renaming ((:@append :fields <renaming>))
       :inline <inline> :non-memoizable <non-memoizable>)

     (acl2::def-ruleset! <stobjname>-defs nil)

     (:@append :fields
      (:@ :fix
       (define <access> ((:@ :arrayp (i natp)) <stobjname>)
         (:@ :arrayp :guard (< i (<stobjname>-><field>-length <stobjname>)))
         :inline t
         :returns (<field> (<pred> <field>) :rule-classes <rule-classes>)
         (the <elt-type>
              (mbe :logic (non-exec (<fix> (<base-access> (:@ :arrayp i) <stobjname>)))
                   :exec (<base-access> (:@ :arrayp i) <stobjname>)))
         ///
         (acl2::add-to-ruleset! <stobjname>-defs <access>))
       (:@ :not-stobjp
        (define <update> ((:@ :arrayp (i natp))
                          (<field> (<pred> <field>) :type <elt-type>)
                          <stobjname>)
          (:@ :arrayp :guard (< i (<stobjname>-><field>-length <stobjname>)))
          :inline t
          :split-types t
          ;; :returns (new-<stobjname> <stobjpred> :hyp (<stobjpred> <stobjname>))
          (mbe :logic (<base-update> (:@ :arrayp i) (<fix> <field>) <stobjname>)
               :exec (<base-update> (:@ :arrayp i) <field> <stobjname>))
         ///
         (acl2::add-to-ruleset! <stobjname>-defs <update>))))

      ;; (:@ (or (not :fix) (not :not-stobjp))
      ;;  (defthm <stobjpred>-of-<update>
      ;;    (implies (and (<pred> <field>)
      ;;                  (:@ :arrayp
      ;;                   (< (nfix i) (<stobjname>-><field>-length <stobjname>)))
      ;;                  (<stobjpred> <stobjname>))
      ;;             (<stobjpred> (<update> (:@ :arrayp i) <field> <stobjname>)))))
      )

     (std::defenum <fieldp> ((:@proj :fields :<field>)))

     (define <get> ((key <fieldp>) <stobjname>)
       :non-executable t
       :hooks ((:fix :hints (("goal" :in-theory (enable <field-fix>)))))
       (case key
         (:@proj :fields
          (:<fieldcase>
           (:@ :not-arrayp (<access> <stobjname>))
           (:@ :arrayp (nth *<base-access>* <stobjname>))))))

     (defsection <stobjname>-field-basics
       (local (in-theory (enable <get>
                                 <field-fix>
                                 <stobjpred>
                                 (:@append :fields
                                  (:@ :fix
                                   <access>
                                   <update>)))))

       (:@append :fields
        (def-updater-independence-thm <access>-of-update
          (implies (equal (<get> :<field> new)
                          (<get> :<field> old))
                   (equal (<access> (:@ :arrayp i) new)
                          (<access> (:@ :arrayp i) old))))

        (defthm <update>-preserves-others
          (implies (not (equal (<field-fix> key) :<field>))
                   (equal (<get> key (<update> (:@ :arrayp i) <field> <stobjname>))
                          (<get> key <stobjname>))))

        
        (defthm <update>-self-identity
          (implies (and (<stobjpred> <stobjname>)
                        (:@ :arrayp (< (nfix i) (<length> <stobjname>))))
                   (equal (<update> (:@ :arrayp i) (<access> (:@ :arrayp i) <stobjname>) <stobjname>)
                          <stobjname>))
          :hints(("Goal" :in-theory (enable redundant-update-nth))))

        (defthm <access>-of-<update>
          (equal (<access> (:@ :arrayp i) (<update> (:@ :arrayp i) <field> <stobjname>))
                 (:@ :fix (<fix> <field>))
                 (:@ :no-fix <field>)))

        (:@ :arrayp
         (defthm <access>-of-<update>-diff
           (implies (not (equal (nfix i) (nfix j)))
                    (equal (<access> i (<update> j <field> <stobjname>))
                           (<access> i <stobjname>))))

         (defthmd <access>-of-<update>-split
           (equal (<access> i (<update> j <field> <stobjname>))
                  (if (equal (nfix i) (nfix j))
                      (:@ :fix (<fix> <field>))
                    (:@ :no-fix <field>)
                    (<access> i <stobjname>))))

         (def-updater-independence-thm <length>-of-update
           (implies (equal (<get> :<field> new)
                           (<get> :<field> old))
                    (equal (<length> new)
                           (<length> old))))

         (defthm <length>-of-<update>
           (implies (< (nfix i) (<length> <stobjname>))
                    (equal (<length> (<update> i <field> <stobjname>))
                           (<length> <stobjname>))))


         (local (defthm nth-when-<recognizer>
                  (implies (and (<recognizer> x)
                                (:@ :not-elementp-of-nil (< (nfix i) (len x))))
                           (<pred> (nth i x)))
                  :hints(("Goal" :in-theory (enable nth)))))
                           

         (:@ :resizable
          (defthm <resize>-preserves-others
            (implies (not (equal (<field-fix> key) :<field>))
                     (equal (<get> key (<resize> size <stobjname>))
                            (<get> key <stobjname>))))
          
          (defthm <length>-of-<resize>
            (equal (<length> (<resize> size <stobjname>))
                   (nfix size)))))

        (:@ (and :no-fix :pred)
         (defthm <access>-type
           (implies (and (<stobjpred> <stobjname>)
                         (:@ (and :arrayp :not-elementp-of-nil)
                          (< (nfix i) (<length> <stobjname>))))
                    (<pred> (<access> (:@ :arrayp i) <stobjname>)))
           :hints(("Goal" :in-theory (enable <access>)))
           :rule-classes <rule-classes>)))

       
       (acl2::add-to-ruleset! <stobjname>-defs
                              '(<stobjpred>
                                (:@append :fields
                                 <base-access> <base-update>
                                 (:@ :arrayp
                                  <length> <resize>))))
       (in-theory (disable* <stobjname>-defs
                   ;; <stobjpred>
                   ;; (:@append :fields
                   ;;  <base-access> <base-update>
                   ;;  (:@ :arrayp
                   ;;   <length> <resize>))
                   )))))


(defun defnicestobj-fn (name args state)
  (declare (xargs :stobjs state))
  (b* (((nicestobj x) (parse-nicestobj name args (w state))))
    (acl2::template-subst-top *nicestobj-template* x.template)))
       
(defmacro defnicestobj (name &rest args)
  `(make-event
    (defnicestobj-fn ',name ',args state)))

(logic)


(defthmd redundant-update-nth
  (implies (< (nfix n) (len x))
           (equal (update-nth n (nth n x) x)
                  x))
  :hints(("Goal" :in-theory (enable update-nth nth))))

(local (defthm len-of-resize-list
         (equal (len (Resize-list x size default))
                (nfix size))))

(local (in-theory (disable update-nth nth)))


(local (defnicestobj foo
         (nat :type (integer 0 *) :pred natp :fix nfix :initially 0 :rule-classes :type-prescription)
         (str :type string :fix acl2::str-fix :initially "")
         (grumble :type (integer 5 *) :initially 5)
         (any :initially buz)
         (fa :type (array (integer 0 *) (0)) :pred natp :fix nfix :initially 1 :rule-classes :type-prescription)
         (fb :type (array string (0)) :initially "hi" :rule-classes :type-prescription
             :resizable t)))

(local (defnicestobj bar
         (nat :type (integer 0 *) :pred natp :fix nfix :initially 0 :rule-classes :type-prescription)
         (str :type string :fix acl2::str-fix :initially "")
         (foo :type foo)
         (grumble :type (integer 5 *) :initially 5)
         (foos :type (array foo (0)) :resizable t)
         (any :initially buz)))

        
