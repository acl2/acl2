;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "deflist")
(include-book "symbol-listp")
(include-book "tuple-listp")
(include-book "cons-listp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (defaggregate name
;;   (field1 ... fieldN)
;;   :require ((natp-of-field1            (natp field1))
;;             (less-of-field1-and-field2 (< field1 field2))
;;              ...
;;             (barp-of-fieldN            (barp fieldN)))
;;   :legiblep t)

(defun constructor-name (base-name)
  (declare (xargs :mode :program))
  base-name)

(defun accessor-name (base-name field)
  (declare (xargs :mode :program))
  (ACL2::mksym base-name '-> field))

(defun recognizer-name (base-name)
  (declare (xargs :mode :program))
  (ACL2::mksym base-name 'p))



;; We can lay out the components of the structure in either "legibly" by using
;; maps with named keys, or "illegibly" by using a tree structure.  Illegible
;; structures are more efficient, but are not very convenient when you are
;; trying to debug your code.  By default, we lay out the structure legibly.

(defun illegible-split-fields (fields)
  ;; Convert a linear list of fields into a balanced tree with the same fields
  (declare (xargs :mode :program))
  (let ((length (len fields)))
    (cond ((equal length 1)
           (first fields))
          ((equal length 2)
           (cons (first fields) (second fields)))
          (t
           (let* ((halfway   (ACL2::floor length 2))
                  (firsthalf (ACL2::take halfway fields))
                  (lasthalf  (ACL2::nthcdr halfway fields)))
             (cons (illegible-split-fields firsthalf)
                   (illegible-split-fields lasthalf)))))))

(defun illegible-fields-map-aux (split-fields path)
  ;; Convert the balanced tree into a map from field names to paths, e.g.,
  ;; field1 might be bound to (car (car x)), field2 to (cdr (car x)), etc.
  (declare (xargs :mode :program))
  (if (consp split-fields)
      (fast-app (illegible-fields-map-aux (car split-fields) `(car ,path))
                (illegible-fields-map-aux (cdr split-fields) `(cdr ,path)))
    (list (cons split-fields path))))

(defun illegible-fields-map (fields)
  ;; Convert a linear list of fields into a map from field names to paths.
  (declare (xargs :mode :program))
  (illegible-fields-map-aux (illegible-split-fields fields) 'x))

(defun illegible-structure-checks-aux (split-fields path)
  ;; Convert the balanced tree into a list of the consp checks we'll need.
  (declare (xargs :mode :program))
  (if (consp split-fields)
      (cons `(consp ,path)
            (app (illegible-structure-checks-aux (car split-fields) `(car ,path))
                 (illegible-structure-checks-aux (cdr split-fields) `(cdr ,path))))
    nil))

(defun illegible-structure-checks (fields)
  ;; Convert a linear list of fields into the consp checks we'll need.
  (declare (xargs :mode :program))
  (illegible-structure-checks-aux (illegible-split-fields fields) 'x))

(defun illegible-pack-aux (split-fields)
  ;; Convert the tree of split fields into a cons tree for building the struct.
  (declare (xargs :mode :program))
  (if (consp split-fields)
      `(cons ,(illegible-pack-aux (car split-fields))
             ,(illegible-pack-aux (cdr split-fields)))
    split-fields))

(defun illegible-pack-fields (fields)
  ;; Convert a linear list of fields into consing code
  (declare (xargs :mode :program))
  (illegible-pack-aux (illegible-split-fields fields)))



(defun legible-fields-map (fields)
  ;; Convert a linear list of fields into a map from field names to paths.
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (cons (car fields) `(cdr (lookup ',(car fields) x)))
            (legible-fields-map (cdr fields)))
    nil))

(defun legible-pack-fields-aux (fields)
  ;; Convert a linear list of fields into the pairs for a list operation
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons `(cons ',(car fields) ,(car fields))
            (legible-pack-fields-aux (cdr fields)))
    nil))

(defun legible-pack-fields (fields)
  ;; Convert a linear list of fields into consing code for a legible map
  (declare (xargs :mode :program))
  `(list ,@(legible-pack-fields-aux fields)))



(defun fields-map (legiblep fields)
  ;; Create a fields map of the appropriate type
  (declare (xargs :mode :program))
  (if legiblep
      (legible-fields-map fields)
    (illegible-fields-map fields)))

(defun pack-fields (legiblep fields)
  ;; Create a fields map of the appropriate type
  (declare (xargs :mode :program))
  (if legiblep
      (legible-pack-fields fields)
    (illegible-pack-fields fields)))

(defun structure-checks (legiblep fields)
  ;; Check that the object has the appropriate cons structure
  (declare (xargs :mode :program))
  (if legiblep
      '((mapp x)
        (consp x))
    (illegible-structure-checks fields)))



(defun fields-map-let-bindings (map)
  ;; Convert a fields map into a list of let bindings
  (declare (xargs :mode :program))
  (if (consp map)
      (let* ((entry (car map))
             (field (car entry))
             (path  (cdr entry)))
        (cons (list field path)
              (fields-map-let-bindings (cdr map))))
    nil))

(defun make-constructor (name fields require legiblep)
  (declare (xargs :mode :program))
  `(definlined ,(constructor-name name) ,fields
    (declare (xargs :guard (and ,@(strip-seconds require))))
    ,(pack-fields legiblep fields)))

(defun make-recognizer (name fields require legiblep)
  (declare (xargs :mode :program))
  `(defund ,(recognizer-name name) (x)
     (declare (xargs :guard t))
     (and ,@(structure-checks legiblep fields)
          (let ,(fields-map-let-bindings (fields-map legiblep fields))
            (declare (ACL2::ignorable ,@fields))
            (and ,@(strip-seconds require))))))

(defun make-accessor (name field map)
  (declare (xargs :mode :program))
  `(definlined ,(accessor-name name field) (x)
     (declare (xargs :guard (,(recognizer-name name) x)
                     :guard-hints (("Goal" :in-theory (enable ,(recognizer-name name))))))
     ,(cdr (lookup field map))))

(defun make-accessors-aux (name fields map)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (make-accessor name (car fields) map)
            (make-accessors-aux name (cdr fields) map))
    nil))

(defun make-accessors (name fields legiblep)
  (declare (xargs :mode :program))
  (make-accessors-aux name fields (fields-map legiblep fields)))

(defun make-accessor-of-constructor (name field all-fields)
  (declare (xargs :mode :program))
  `(defthm ,(ACL2::mksym (accessor-name name field) '-of- (constructor-name name))
     (equal (,(accessor-name name field) (,(constructor-name name) ,@all-fields))
            ,field)
     :hints(("Goal" :in-theory (enable ,(accessor-name name field)
                                       ,(constructor-name name))))))

(defun make-accessors-of-constructor-aux (name fields all-fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (make-accessor-of-constructor name (car fields) all-fields)
            (make-accessors-of-constructor-aux name (cdr fields) all-fields))
    nil))

(defun make-accessors-of-constructor (name fields)
  (declare (xargs :mode :program))
  (make-accessors-of-constructor-aux name fields fields))


(defun fields-recognizer-map (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (cons (car fields) (list (accessor-name name (car fields)) 'x))
            (fields-recognizer-map name (cdr fields)))
    nil))

(defun accessor-names (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (accessor-name name (car fields))
            (accessor-names name (cdr fields)))
    nil))

(defun make-requirement-of-recognizer (name require map accnames)
  (declare (xargs :mode :program))
  `(defthm ,(ACL2::mksym 'forcing- (first require))
     (implies (force (,(recognizer-name name) x))
              (equal ,(ACL2::sublis map (second require))
                     t))
     :hints(("Goal" :in-theory (enable ,(recognizer-name name) ,@accnames)))))

(defun make-requirements-of-recognizer-aux (name require map accnames)
  (declare (xargs :mode :program))
  (if (consp require)
      (cons (make-requirement-of-recognizer name (car require) map accnames)
            (make-requirements-of-recognizer-aux name (cdr require) map accnames))
    nil))

(defun make-requirements-of-recognizer (name require fields)
  (declare (xargs :mode :program))
  (make-requirements-of-recognizer-aux name require
                                       (fields-recognizer-map name fields)
                                       (accessor-names name fields)))



(defun changer-args-to-alist (args valid-fields)
  (declare (xargs :mode :program))
  (if (consp args)
      (and (consp (cdr args))
           (let ((field (first args))
                 (value (second args)))
             (and (or (memberp field valid-fields)
                      (ACL2::er hard? 'changer-args-to-alist
                                "~x0 is not among the allowed fields, ~&0." valid-fields))
                  (cons (cons field value)
                        (changer-args-to-alist (cdr (cdr args)) valid-fields)))))
    nil))

(defun make-valid-fields-for-changer (fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (ACL2::intern-in-package-of-symbol (ACL2::symbol-name (car fields)) :keyword)
            (make-valid-fields-for-changer (cdr fields)))
    nil))



(defun changer-fn-name (name)
  (declare (xargs :mode :program))
  (ACL2::mksym 'change- name '-fn))

(defun changer-name (name)
  (declare (xargs :mode :program))
  (ACL2::mksym 'change- name))

(defun make-changer-fn-aux (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (let ((kwd-name (ACL2::intern-in-package-of-symbol (ACL2::symbol-name (car fields)) :keyword)))
        (cons `(if (lookup ,kwd-name alist)
                   (cdr (lookup ,kwd-name alist))
                 (list ',(accessor-name name (car fields)) x))
              (make-changer-fn-aux name (cdr fields))))
    nil))

(defun make-changer-fn (name fields)
  (declare (xargs :mode :program))
  `(defun ,(changer-fn-name name) (x alist)
     (declare (xargs :mode :program))
     (cons ',(constructor-name name)
           ,(cons 'list (make-changer-fn-aux name fields)))))

(defun make-changer (name fields)
  (declare (xargs :mode :program))
  `(defmacro ,(changer-name name) (x &rest args)
     (,(changer-fn-name name) x (changer-args-to-alist args ',(make-valid-fields-for-changer fields)))))





(defmacro defaggregate (name fields &key require (legiblep ''t))
  (and (or (symbolp name)
           (ACL2::er hard 'defaggregate "Name must be a symbol.~%"))
       (or (symbol-listp fields)
           (ACL2::er hard 'defaggregate "Fields must be a list of symbols.~%"))
       (or (uniquep fields)
           (ACL2::er hard 'defaggregate "Fields must be unique.~%"))
       (or (consp fields)
           (ACL2::er hard 'defaggregate "There must be at least one field.~%"))
       (or (and (tuple-listp 2 require)
                (symbol-listp (strip-firsts require)))
           (ACL2::er hard 'defaggregate ":require must be a list of (name requirement) tuples.~%"))
       (or (uniquep (strip-firsts require))
           (ACL2::er hard 'defaggregate "The names given to :require must be unique.~%"))
       (or (cons-listp (strip-seconds require))
           (ACL2::er hard 'defaggregate "The requirements must be at least conses.~%"))
       (or (ACL2::pseudo-term-listp (strip-seconds require))
           (ACL2::er hard 'defaggregate "The requierments must be terms.~%"))
       (let ((foop (recognizer-name name))
             (make-foo (constructor-name name)))
         `(encapsulate
           ()
           ,(make-recognizer name fields require legiblep)
           ,(make-constructor name fields require legiblep)
           ,@(make-accessors name fields legiblep)

           (defthm ,(ACL2::mksym make-foo '-under-iff)
             (iff (,make-foo ,@fields)
                  t)
             :hints(("Goal" :in-theory (enable ,make-foo))))

           (defthm ,(ACL2::mksym 'booleanp-of- foop)
             (equal (booleanp (,foop x))
                    t)
             :hints(("Goal" :in-theory (enable ,foop))))

           ,(if (consp require)
                `(defthm ,(ACL2::mksym 'forcing- foop '-of- make-foo)
                   (implies (force (and ,@(strip-seconds require)))
                            (equal (,foop (,make-foo ,@fields))
                                   t))
                   :hints(("Goal" :in-theory (enable ,foop ,make-foo))))
              `(defthm ,(ACL2::mksym foop '-of- make-foo)
                 (equal (,foop (,make-foo ,@fields))
                        t)
                 :hints(("Goal" :in-theory (enable ,foop ,make-foo)))))

           ,@(make-accessors-of-constructor name fields)

           ,@(make-requirements-of-recognizer name require fields)

           ,(make-changer-fn name fields)
           ,(make-changer name fields)

           ))))

#|
(defaggregate taco
  (lettuce shell meat cheese)
  :require
  ((taco-cheese-is-okay (memberp cheese '(cheddar swiss)))))

(change-taco (taco 'iceberg 'hard 'beans 'cheddar)
             :lettuce 'arugula
             :meat 'dog)
|#