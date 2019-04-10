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
    :access
    :base-access
    :update
    :base-update
    :resize
    :length

    ;; only applicable to add-ons/hash-stobjs.lisp hash table fields
    :boundp
    :access?
    :remove
    :count
    :clear
    :init))

(defconst *nicestobj-field-keys*
  (append '(:name :arrayp :hashp :rename-update :stobjp) *nicestobj-field-userkeys*))



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
  (b* ((stobj (or (fgetprop x 'acl2::congruent-stobj-rep nil wrld) x)))
    (nth 1 (fgetprop stobj 'acl2::stobj nil wrld))))

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
       ((when (and (consp type) (member-eq (car type) '(array acl2::hash-table))))
        (raise "Nicestobj doesn't support array or hash-table fields yet~%"))
       (type-pred (acl2::translate-declaration-to-guard type name nil))
       ;; (typep (and type-pred (not (member-eq-tree 'satisfies type))))
       (stobj-pred (and (not type-pred)
                        (symbolp type)
                        (congruent-stobj-pred type wrld)))
       (type-pred-expr (or type-pred 
                           (and stobj-pred
                                `(,stobj-pred ,name))))
       (type-pred-fn (and type-pred-expr
                          ;; special case for when the type is T
                          (member-eq-tree name type-pred-expr)
                          `(lambda (,name) ,type-pred-expr)))
       (kwd-alist (cons (cons :stobjp stobj-pred) kwd-alist))
       (kwd-alist (kwd-alist-add-default :key (intern-in-package-of-symbol (symbol-name name) :foo) kwd-alist))
       (kwd-alist (kwd-alist-add-default :pred type-pred-fn kwd-alist)) 
       (kwd-alist (kwd-alist-add-default :rule-classes :rewrite kwd-alist))
       (kwd-alist (kwd-alist-add-default :access
                                         (intern-in-package-of-symbol
                                          (concatenate 'string (symbol-name stobjname) "->"
                                                       (symbol-name name))
                                          stobjname)
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :base-access
                                         (if (cdr (assoc :fix kwd-alist))
                                             (intern-in-package-of-symbol
                                              (concatenate 'string (symbol-name stobjname) "->"
                                                           (symbol-name name) "^")
                                              stobjname)
                                           (cdr (assoc :access kwd-alist)))
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :update
                                         (intern-in-package-of-symbol
                                          (concatenate 'string "UPDATE-"
                                                       (symbol-name stobjname) "->"
                                                       (symbol-name name))
                                          stobjname)
                                         kwd-alist))
       (kwd-alist (kwd-alist-add-default :base-update
                                         (if (and (cdr (assoc :fix kwd-alist))
                                                  (not stobj-pred))
                                             (intern-in-package-of-symbol
                                              (concatenate 'string "UPDATE-"
                                                           (symbol-name stobjname) "->"
                                                           (symbol-name name)
                                                           "^")
                                              stobjname)
                                           (cdr (assoc :update kwd-alist)))
                                         kwd-alist))
       (kwd-alist (cons (cons :rename-update
                              (not (eq (cdr (assoc :base-update kwd-alist))
                                       ;; from ACL2 source function
                                       ;; defstobj-fnname, this is the name of
                                       ;; the updater for the given field
                                       (acl2::packn-pos (list "UPDATE-"
                                                              (cdr (assoc :base-access kwd-alist)))
                                                        (cdr (assoc :base-access kwd-alist))))))
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
                       (if field.rename-update '(:rename-updater) '(:no-rename-updater))
                       (if field.stobjp '(:stobjp) '(:not-stobjp)))
     :atoms `((<field> . ,field.name)
              (<stobjname> . ,stobjname)
              (:<field> . ,field.key)
              (:<fieldcase> . ,(if lastp t field.key))
              (<type> . ,field.type)
              (<initially> . ,field.initially)
              (<pred> . ,field.pred)
              (<fix> . ,field.fix)
              (<access> . ,field.access)
              (<update> . ,field.update)
              (<base-access> . ,field.base-access)
              (<base-update> . ,field.base-update)
              (<rule-classes> . ,field.rule-classes))
     :strs `(("<FIELD>" . ,(symbol-name field.name))
             ("<ACCESS>" . ,(symbol-name field.access))
             ("<UPDATE>" . ,(symbol-name field.update)))
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
                   :strs `(("<STOBJNAME>" . ,(symbol-name stobjname)))
                   :features (if x.rename-pred '(:rename-pred) '(:no-rename-pred))))
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
        (<base-access> :type <type> (:@ :not-stobjp :initially <initially>)))
       :inline <inline> :non-memoizable <non-memoizable>)

     (:@append :fields
      (:@ :fix
       (define <access> (<stobjname>)
         :inline t
         :returns (<field> (<pred> <field>) :rule-classes <rule-classes>)
         (the <type>
              (mbe :logic (non-exec (<fix> (<base-access> <stobjname>)))
                   :exec (<base-access> <stobjname>))))
       (:@ :not-stobjp
        (define <update> ((<field> (<pred> <field>) :type <type>)
                          <stobjname>)
          :inline t
          :split-types t
          (mbe :logic (<base-update> (<fix> <field>) <stobjname>)
               :exec (<base-update> <field> <stobjname>))))))

     (std::defenum <fieldp> ((:@proj :fields :<field>)))

     (define <get> ((key <fieldp>) <stobjname>)
       :non-executable t
       :hooks ((:fix :hints (("goal" :in-theory (enable <field-fix>)))))
       (case key
         (:@proj :fields
          (:<fieldcase> (<access> <stobjname>)))))

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
                   (equal (<access> new)
                          (<access> old))))

        (defthm <update>-preserves-others
          (implies (not (equal (<field-fix> key) :<field>))
                   (equal (<get> key (<update> <field> <stobjname>))
                          (<get> key <stobjname>))))

        
        (defthm <update>-self-identity
          (implies (<stobjpred> <stobjname>)
                   (equal (<update> (<access> <stobjname>) <stobjname>)
                          <stobjname>))
          :hints(("Goal" :in-theory (enable redundant-update-nth))))

        (defthm <access>-of-<update>
          (equal (<access> (<update> <field> <stobjname>))
                 (:@ :fix (<fix> <field>))
                 (:@ :no-fix <field>)))

        (:@ (and :no-fix :pred)
         (defthm <access>-type
           (implies (<stobjpred> <stobjname>)
                    (<pred> (<access> <stobjname>)))
           :hints(("Goal" :in-theory (enable <access>)))
           :rule-classes <rule-classes>)))

       (in-theory (disable
                   <stobjpred>
                   (:@append :fields <base-access> <base-update>))))))


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

(local (defnicestobj foo
         (nat :type (integer 0 *) :pred natp :fix nfix :initially 0 :rule-classes :type-prescription)
         (str :type string :fix acl2::str-fix :initially "")
         (grumble :type (integer 5 *) :initially 5)
         (any :initially buz)))

(local (defnicestobj bar
         (nat :type (integer 0 *) :pred natp :fix nfix :initially 0 :rule-classes :type-prescription)
         (str :type string :fix acl2::str-fix :initially "")
         (foo :type foo)
         (grumble :type (integer 5 *) :initially 5)
         (any :initially buz)))

        
