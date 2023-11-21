;;;; ---------------------------------------------------------------------------
;;;; ASDF package upgrade, including implementation-dependent magic.
;;
;; See https://bugs.launchpad.net/asdf/+bug/485687
;;

;; CAUTION: The definition of the UIOP/PACKAGE package MUST NOT CHANGE,
;; NOT NOW, NOT EVER, NOT UNDER ANY CIRCUMSTANCE. NEVER.
;; ... and the same goes for UIOP/PACKAGE-LOCAL-NICKNAMES.
;;
;; The entire point of UIOP/PACKAGE is to address the fact that the CL standard
;; *leaves it unspecified what happens when a package is redefined incompatibly*.
;; For instance, SBCL 1.4.2 will signal a full WARNING when this happens,
;; throwing a wrench in upgrading code with ASDF itself, while continuing to
;; export old symbols it now shouldn't as it also exports new ones,
;; causing problems with code that relies on the new/current exports.
;; CLISP and CCL also exports both sets of symbols, though without any WARNING.
;; ABCL 1.6.1 will plainly ignore the new definition.
;; Other implementations may do whatever they want and change their behavior at any time.
;; ***Using DEFPACKAGE twice with different definitions is nasal-demon territory.***
;;
;; Thus we define UIOP/PACKAGE:DEFINE-PACKAGE with which packages can be defined
;; in an upgrade-friendly way: the new definition is authoritative, and
;; the package will define and export exactly those symbols in the new definition,
;; no more and no fewer, whereas it is well-defined what happens to previous symbols.
;; However, for obvious bootstrap reasons, we cannot use DEFINE-PACKAGE
;; to define UIOP/PACKAGE itself, only DEFPACKAGE.
;; Therefore, unlike the other packages in ASDF, UIOP/PACKAGE is immutable,
;; now and forever. It is frozen for the aeons to come, like the CL package itself,
;; to the same exact state it was defined at its inception, in ASDF 2.27 in 2013.
;; The same goes for UIOP/PACKAGE-LOCAL-NICKNAMES, that we use internally.
;;
;; If you ever must define new symbols in this file, you can and must
;; export them from a different package, possibly defined in the same file,
;; say a package UIOP/PACKAGE* defined at the end of this file with DEFINE-PACKAGE,
;; that might use :import-from to import the symbols from UIOP/PACKAGE,
;; if you must somehow define them in UIOP/PACKAGE.

(defpackage :uiop/package ;;; THOU SHALT NOT modify this definition, EVER. See explanations above.
  (:use :common-lisp)
  (:export
   #:find-package* #:find-symbol* #:symbol-call
   #:intern* #:export* #:import* #:shadowing-import* #:shadow* #:make-symbol* #:unintern*
   #:symbol-shadowing-p #:home-package-p
   #:symbol-package-name #:standard-common-lisp-symbol-p
   #:reify-package #:unreify-package #:reify-symbol #:unreify-symbol
   #:nuke-symbol-in-package #:nuke-symbol #:rehome-symbol
   #:ensure-package-unused #:delete-package*
   #:package-names #:packages-from-names #:fresh-package-name #:rename-package-away
   #:package-definition-form #:parse-define-package-form
   #:ensure-package #:define-package
   ))

(in-package :uiop/package)

;;; package local nicknames feature.
;;; This can't be deferred until common-lisp.lisp, where most such features are set.
;;; ABCL and CCL already define this feature appropriately.
;;; Seems to be unconditionally present for SBCL, ACL, and CLASP
;;; Don't know about ECL, or others
(eval-when (:load-toplevel :compile-toplevel :execute)
  ;; ABCL pushes :package-local-nicknames without UIOP interfering,
  ;; and Lispworks will do so
  #+(or sbcl clasp)
  (pushnew :package-local-nicknames *features*)
  #+allegro
  (let ((fname (find-symbol (symbol-name '#:add-package-local-nickname) '#:excl)))
    (when (and fname (fboundp fname))
      (pushnew :package-local-nicknames *features*))))

;;; THOU SHALT NOT modify this definition, EVER, *EXCEPT* to add a new implementation.
;; If you somehow need to modify the API in any way,
;; you will need to create another, differently named, and just as immutable package.
#+package-local-nicknames
(defpackage :uiop/package-local-nicknames
  (:use :cl)
  (:import-from
   #+allegro #:excl
   #+sbcl #:sb-ext
   #+(or clasp abcl ecl) #:ext
   #+ccl #:ccl
   #+lispworks #:hcl
   #-(or allegro sbcl clasp abcl ccl lispworks ecl)
   (error "Don't know from which package this lisp supplies the local-package-nicknames API.")
   #:remove-package-local-nickname #:package-local-nicknames #:add-package-local-nickname)
  (:export
   #:add-package-local-nickname #:remove-package-local-nickname #:package-local-nicknames))

;;;; General purpose package utilities

(eval-when (:load-toplevel :compile-toplevel :execute)
  (deftype package-designator () '(and (or package character string symbol) (satisfies find-package)))
  (define-condition no-such-package-error (type-error)
    ()
    (:default-initargs :expected-type 'package-designator)
    (:report (lambda (c s)
              (format s "No package named ~a" (string (type-error-datum c))))))

  (defmethod package-designator ((c no-such-package-error))
    (type-error-datum c))

  (defun find-package* (package-designator &optional (errorp t))
    "Like CL:FIND-PACKAGE, but by default raises a UIOP:NO-SUCH-PACKAGE-ERROR if the
  package is not found."
    (let ((package (find-package package-designator)))
      (cond
        (package package)
        (errorp (error 'no-such-package-error :datum package-designator))
        (t nil))))

  (defun find-symbol* (name package-designator &optional (error t))
    "Find a symbol in a package of given string'ified NAME;
unlike CL:FIND-SYMBOL, work well with 'modern' case sensitive syntax
by letting you supply a symbol or keyword for the name;
also works well when the package is not present.
If optional ERROR argument is NIL, return NIL instead of an error
when the symbol is not found."
    (block nil
      (let ((package (find-package* package-designator error)))
        (when package ;; package error handled by find-package* already
          (multiple-value-bind (symbol status) (find-symbol (string name) package)
            (cond
              (status (return (values symbol status)))
              (error (error "There is no symbol ~S in package ~S" name (package-name package))))))
        (values nil nil))))
  (defun symbol-call (package name &rest args)
    "Call a function associated with symbol of given name in given package,
with given ARGS. Useful when the call is read before the package is loaded,
or when loading the package is optional."
    (apply (find-symbol* name package) args))
  (defun intern* (name package-designator &optional (error t))
    (intern (string name) (find-package* package-designator error)))
  (defun export* (name package-designator)
    (let* ((package (find-package* package-designator))
           (symbol (intern* name package)))
      (export (or symbol (list symbol)) package)))
  (defun import* (symbol package-designator)
    (import (or symbol (list symbol)) (find-package* package-designator)))
  (defun shadowing-import* (symbol package-designator)
    (shadowing-import (or symbol (list symbol)) (find-package* package-designator)))
  (defun shadow* (name package-designator)
    (shadow (list (string name)) (find-package* package-designator)))
  (defun make-symbol* (name)
    (etypecase name
      (string (make-symbol name))
      (symbol (copy-symbol name))))
  (defun unintern* (name package-designator &optional (error t))
    (block nil
      (let ((package (find-package* package-designator error)))
        (when package
          (multiple-value-bind (symbol status) (find-symbol* name package error)
            (cond
              (status (unintern symbol package)
                      (return (values symbol status)))
              (error (error "symbol ~A not present in package ~A"
                            (string symbol) (package-name package))))))
        (values nil nil))))
  (defun symbol-shadowing-p (symbol package)
    (and (member symbol (package-shadowing-symbols package)) t))
  (defun home-package-p (symbol package)
    (and package (let ((sp (symbol-package symbol)))
                   (and sp (let ((pp (find-package* package)))
                             (and pp (eq sp pp))))))))


(eval-when (:load-toplevel :compile-toplevel :execute)
  (defun symbol-package-name (symbol)
    (let ((package (symbol-package symbol)))
      (and package (package-name package))))
  (defun standard-common-lisp-symbol-p (symbol)
    (multiple-value-bind (sym status) (find-symbol* symbol :common-lisp nil)
      (and (eq sym symbol) (eq status :external))))
  (defun reify-package (package &optional package-context)
    (if (eq package package-context) t
        (etypecase package
          (null nil)
          ((eql (find-package :cl)) :cl)
          (package (package-name package)))))
  (defun unreify-package (package &optional package-context)
    (etypecase package
      (null nil)
      ((eql t) package-context)
      ((or symbol string) (find-package package))))
  (defun reify-symbol (symbol &optional package-context)
    (etypecase symbol
      ((or keyword (satisfies standard-common-lisp-symbol-p)) symbol)
      (symbol (vector (symbol-name symbol)
                      (reify-package (symbol-package symbol) package-context)))))
  (defun unreify-symbol (symbol &optional package-context)
    (etypecase symbol
      (symbol symbol)
      ((simple-vector 2)
       (let* ((symbol-name (svref symbol 0))
              (package-foo (svref symbol 1))
              (package (unreify-package package-foo package-context)))
         (if package (intern* symbol-name package)
             (make-symbol* symbol-name)))))))

(eval-when (:load-toplevel :compile-toplevel :execute)
  (defvar *all-package-happiness* '())
  (defvar *all-package-fishiness* (list t))
  (defun record-fishy (info)
    ;;(format t "~&FISHY: ~S~%" info)
    (push info *all-package-fishiness*))
  (defmacro when-package-fishiness (&body body)
    `(when *all-package-fishiness* ,@body))
  (defmacro note-package-fishiness (&rest info)
    `(when-package-fishiness (record-fishy (list ,@info)))))

(eval-when (:load-toplevel :compile-toplevel :execute)
  #+(or clisp clozure)
  (defun get-setf-function-symbol (symbol)
    #+clisp (let ((sym (get symbol 'system::setf-function)))
              (if sym (values sym :setf-function)
                  (let ((sym (get symbol 'system::setf-expander)))
                    (if sym (values sym :setf-expander)
                        (values nil nil)))))
    #+clozure (gethash symbol ccl::%setf-function-names%))
  #+(or clisp clozure)
  (defun set-setf-function-symbol (new-setf-symbol symbol &optional kind)
    #+clisp (assert (member kind '(:setf-function :setf-expander)))
    #+clozure (assert (eq kind t))
    #+clisp
    (cond
      ((null new-setf-symbol)
       (remprop symbol 'system::setf-function)
       (remprop symbol 'system::setf-expander))
      ((eq kind :setf-function)
       (setf (get symbol 'system::setf-function) new-setf-symbol))
      ((eq kind :setf-expander)
       (setf (get symbol 'system::setf-expander) new-setf-symbol))
      (t (error "invalid kind of setf-function ~S for ~S to be set to ~S"
                kind symbol new-setf-symbol)))
    #+clozure
    (progn
      (gethash symbol ccl::%setf-function-names%) new-setf-symbol
      (gethash new-setf-symbol ccl::%setf-function-name-inverses%) symbol))
  #+(or clisp clozure)
  (defun create-setf-function-symbol (symbol)
    #+clisp (system::setf-symbol symbol)
    #+clozure (ccl::construct-setf-function-name symbol))
  (defun set-dummy-symbol (symbol reason other-symbol)
    (setf (get symbol 'dummy-symbol) (cons reason other-symbol)))
  (defun make-dummy-symbol (symbol)
    (let ((dummy (copy-symbol symbol)))
      (set-dummy-symbol dummy 'replacing symbol)
      (set-dummy-symbol symbol 'replaced-by dummy)
      dummy))
  (defun dummy-symbol (symbol)
    (get symbol 'dummy-symbol))
  (defun get-dummy-symbol (symbol)
    (let ((existing (dummy-symbol symbol)))
      (if existing (values (cdr existing) (car existing))
          (make-dummy-symbol symbol))))
  (defun nuke-symbol-in-package (symbol package-designator)
    (let ((package (find-package* package-designator))
          (name (symbol-name symbol)))
      (multiple-value-bind (sym stat) (find-symbol name package)
        (when (and (member stat '(:internal :external)) (eq symbol sym))
          (if (symbol-shadowing-p symbol package)
              (shadowing-import* (get-dummy-symbol symbol) package)
              (unintern* symbol package))))))
  (defun nuke-symbol (symbol &optional (packages (list-all-packages)))
    #+(or clisp clozure)
    (multiple-value-bind (setf-symbol kind)
        (get-setf-function-symbol symbol)
      (when kind (nuke-symbol setf-symbol)))
    (loop :for p :in packages :do (nuke-symbol-in-package symbol p)))
  (defun rehome-symbol (symbol package-designator)
    "Changes the home package of a symbol, also leaving it present in its old home if any"
    (let* ((name (symbol-name symbol))
           (package (find-package* package-designator))
           (old-package (symbol-package symbol))
           (old-status (and old-package (nth-value 1 (find-symbol name old-package))))
           (shadowing (and old-package (symbol-shadowing-p symbol old-package) (make-symbol name))))
      (multiple-value-bind (overwritten-symbol overwritten-symbol-status) (find-symbol name package)
        (unless (eq package old-package)
          (let ((overwritten-symbol-shadowing-p
                  (and overwritten-symbol-status
                       (symbol-shadowing-p overwritten-symbol package))))
            (note-package-fishiness
             :rehome-symbol name
             (when old-package (package-name old-package)) old-status (and shadowing t)
             (package-name package) overwritten-symbol-status overwritten-symbol-shadowing-p)
            (when old-package
              (if shadowing
                  (shadowing-import* shadowing old-package))
              (unintern* symbol old-package))
            (cond
              (overwritten-symbol-shadowing-p
               (shadowing-import* symbol package))
              (t
               (when overwritten-symbol-status
                 (unintern* overwritten-symbol package))
               (import* symbol package)))
            (if shadowing
                (shadowing-import* symbol old-package)
                (import* symbol old-package))
            #+(or clisp clozure)
            (multiple-value-bind (setf-symbol kind)
                (get-setf-function-symbol symbol)
              (when kind
                (let* ((setf-function (fdefinition setf-symbol))
                       (new-setf-symbol (create-setf-function-symbol symbol)))
                  (note-package-fishiness
                   :setf-function
                   name (package-name package)
                   (symbol-name setf-symbol) (symbol-package-name setf-symbol)
                   (symbol-name new-setf-symbol) (symbol-package-name new-setf-symbol))
                  (when (symbol-package setf-symbol)
                    (unintern* setf-symbol (symbol-package setf-symbol)))
                  (setf (fdefinition new-setf-symbol) setf-function)
                  (set-setf-function-symbol new-setf-symbol symbol kind))))
            #+(or clisp clozure)
            (multiple-value-bind (overwritten-setf foundp)
                (get-setf-function-symbol overwritten-symbol)
              (when foundp
                (unintern overwritten-setf)))
            (when (eq old-status :external)
              (export* symbol old-package))
            (when (eq overwritten-symbol-status :external)
              (export* symbol package))))
        (values overwritten-symbol overwritten-symbol-status))))
  (defun ensure-package-unused (package)
    (loop :for p :in (package-used-by-list package) :do
      (unuse-package package p)))
  (defun delete-package* (package &key nuke)
    (let ((p (find-package package)))
      (when p
        (when nuke (do-symbols (s p) (when (home-package-p s p) (nuke-symbol s))))
        (ensure-package-unused p)
        (delete-package package))))
  (defun package-names (package)
    (cons (package-name package) (package-nicknames package)))
  (defun packages-from-names (names)
    (remove-duplicates (remove nil (mapcar #'find-package names)) :from-end t))
  (defun fresh-package-name (&key (prefix :%TO-BE-DELETED)
                               separator
                               (index (random most-positive-fixnum)))
    (loop :for i :from index
          :for n = (format nil "~A~@[~A~D~]" prefix (and (plusp i) (or separator "")) i)
          :thereis (and (not (find-package n)) n)))
  (defun rename-package-away (p &rest keys &key prefix &allow-other-keys)
    (let ((new-name
            (apply 'fresh-package-name
                   :prefix (or prefix (format nil "__~A__" (package-name p))) keys)))
      (record-fishy (list :rename-away (package-names p) new-name))
      (rename-package p new-name))))


;;; Communicable representation of symbol and package information

(eval-when (:load-toplevel :compile-toplevel :execute)
  (defun package-definition-form (package-designator
                                  &key (nicknamesp t) (usep t)
                                    (shadowp t) (shadowing-import-p t)
                                    (exportp t) (importp t) internp (error t))
    (let* ((package (or (find-package* package-designator error)
                        (return-from package-definition-form nil)))
           (name (package-name package))
           (nicknames (package-nicknames package))
           (use (mapcar #'package-name (package-use-list package)))
           (shadow ())
           (shadowing-import (make-hash-table :test 'equal))
           (import (make-hash-table :test 'equal))
           (export ())
           (intern ()))
      (when package
        (loop :for sym :being :the :symbols :in package
              :for status = (nth-value 1 (find-symbol* sym package)) :do
                (ecase status
                  ((nil :inherited))
                  ((:internal :external)
                   (let* ((name (symbol-name sym))
                          (external (eq status :external))
                          (home (symbol-package sym))
                          (home-name (package-name home))
                          (imported (not (eq home package)))
                          (shadowing (symbol-shadowing-p sym package)))
                     (cond
                       ((and shadowing imported)
                        (push name (gethash home-name shadowing-import)))
                       (shadowing
                        (push name shadow))
                       (imported
                        (push name (gethash home-name import))))
                     (cond
                       (external
                        (push name export))
                       (imported)
                       (t (push name intern)))))))
        (labels ((sort-names (names)
                   (sort (copy-list names) #'string<))
                 (table-keys (table)
                   (loop :for k :being :the :hash-keys :of table :collect k))
                 (when-relevant (key value)
                   (when value (list (cons key value))))
                 (import-options (key table)
                   (loop :for i :in (sort-names (table-keys table))
                         :collect `(,key ,i ,@(sort-names (gethash i table))))))
          `(defpackage ,name
             ,@(when-relevant :nicknames (and nicknamesp (sort-names nicknames)))
             (:use ,@(and usep (sort-names use)))
             ,@(when-relevant :shadow (and shadowp (sort-names shadow)))
             ,@(import-options :shadowing-import-from (and shadowing-import-p shadowing-import))
             ,@(import-options :import-from (and importp import))
             ,@(when-relevant :export (and exportp (sort-names export)))
             ,@(when-relevant :intern (and internp (sort-names intern)))))))))


;;; ensure-package, define-package
(eval-when (:load-toplevel :compile-toplevel :execute)
  ;; We already have UIOP:SIMPLE-STYLE-WARNING, but it comes from a later
  ;; package.
  (define-condition define-package-style-warning
      #+sbcl (sb-int:simple-style-warning) #-sbcl (simple-condition style-warning)
      ())
  (defun ensure-shadowing-import (name to-package from-package shadowed imported)
    (check-type name string)
    (check-type to-package package)
    (check-type from-package package)
    (check-type shadowed hash-table)
    (check-type imported hash-table)
    (let ((import-me (find-symbol* name from-package)))
      (multiple-value-bind (existing status) (find-symbol name to-package)
        (cond
          ((gethash name shadowed)
           (unless (eq import-me existing)
             (error "Conflicting shadowings for ~A" name)))
          (t
           (setf (gethash name shadowed) t)
           (setf (gethash name imported) t)
           (unless (or (null status)
                       (and (member status '(:internal :external))
                            (eq existing import-me)
                            (symbol-shadowing-p existing to-package)))
             (note-package-fishiness
              :shadowing-import name
              (package-name from-package)
              (or (home-package-p import-me from-package) (symbol-package-name import-me))
              (package-name to-package) status
              (and status (or (home-package-p existing to-package) (symbol-package-name existing)))))
           (shadowing-import* import-me to-package))))))
  (defun ensure-imported (import-me into-package &optional from-package)
    (check-type import-me symbol)
    (check-type into-package package)
    (check-type from-package (or null package))
    (let ((name (symbol-name import-me)))
      (multiple-value-bind (existing status) (find-symbol name into-package)
        (cond
          ((not status)
           (import* import-me into-package))
          ((eq import-me existing))
          (t
           (let ((shadowing-p (symbol-shadowing-p existing into-package)))
             (note-package-fishiness
              :ensure-imported name
              (and from-package (package-name from-package))
              (or (home-package-p import-me from-package) (symbol-package-name import-me))
              (package-name into-package)
              status
              (and status (or (home-package-p existing into-package) (symbol-package-name existing)))
              shadowing-p)
             (cond
               ((or shadowing-p (eq status :inherited))
                (shadowing-import* import-me into-package))
               (t
                (unintern* existing into-package)
                (import* import-me into-package))))))))
    (values))
  (defun ensure-import (name to-package from-package shadowed imported)
    (check-type name string)
    (check-type to-package package)
    (check-type from-package package)
    (check-type shadowed hash-table)
    (check-type imported hash-table)
    (multiple-value-bind (import-me import-status) (find-symbol name from-package)
      (when (null import-status)
        (note-package-fishiness
         :import-uninterned name (package-name from-package) (package-name to-package))
        (setf import-me (intern* name from-package)))
      (multiple-value-bind (existing status) (find-symbol name to-package)
        (cond
          ((and imported (gethash name imported))
           (unless (and status (eq import-me existing))
             (error "Can't import ~S from both ~S and ~S"
                    name (package-name (symbol-package existing)) (package-name from-package))))
          ((gethash name shadowed)
           (error "Can't both shadow ~S and import it from ~S" name (package-name from-package)))
          (t
           (setf (gethash name imported) t))))
      (ensure-imported import-me to-package from-package)))
  (defun ensure-inherited (name symbol to-package from-package mixp shadowed imported inherited)
    (check-type name string)
    (check-type symbol symbol)
    (check-type to-package package)
    (check-type from-package package)
    (check-type mixp (member nil t)) ; no cl:boolean on Genera
    (check-type shadowed hash-table)
    (check-type imported hash-table)
    (check-type inherited hash-table)
    (multiple-value-bind (existing status) (find-symbol name to-package)
      (let* ((sp (symbol-package symbol))
             (in (gethash name inherited))
             (xp (and status (symbol-package existing))))
        (when (null sp)
          (note-package-fishiness
           :import-uninterned name
           (package-name from-package) (package-name to-package) mixp)
          (import* symbol from-package)
          (setf sp (package-name from-package)))
        (cond
          ((gethash name shadowed))
          (in
           (unless (equal sp (first in))
             (if mixp
                 (ensure-shadowing-import name to-package (second in) shadowed imported)
                 (error "Can't inherit ~S from ~S, it is inherited from ~S"
                        name (package-name sp) (package-name (first in))))))
          ((gethash name imported)
           (unless (eq symbol existing)
             (error "Can't inherit ~S from ~S, it is imported from ~S"
                    name (package-name sp) (package-name xp))))
          (t
           (setf (gethash name inherited) (list sp from-package))
           (when (and status (not (eq sp xp)))
             (let ((shadowing (symbol-shadowing-p existing to-package)))
               (note-package-fishiness
                :inherited name
                (package-name from-package)
                (or (home-package-p symbol from-package) (symbol-package-name symbol))
                (package-name to-package)
                (or (home-package-p existing to-package) (symbol-package-name existing)))
               (if shadowing (ensure-shadowing-import name to-package from-package shadowed imported)
                   (unintern* existing to-package)))))))))
  (defun ensure-mix (name symbol to-package from-package shadowed imported inherited)
    (check-type name string)
    (check-type symbol symbol)
    (check-type to-package package)
    (check-type from-package package)
    (check-type shadowed hash-table)
    (check-type imported hash-table)
    (check-type inherited hash-table)
    (unless (gethash name shadowed)
      (multiple-value-bind (existing status) (find-symbol name to-package)
        (let* ((sp (symbol-package symbol))
               (im (gethash name imported))
               (in (gethash name inherited)))
          (cond
            ((or (null status)
                 (and status (eq symbol existing))
                 (and in (eq sp (first in))))
             (ensure-inherited name symbol to-package from-package t shadowed imported inherited))
            (in
             (remhash name inherited)
             (ensure-shadowing-import name to-package (second in) shadowed imported))
            (im
             (error "Symbol ~S import from ~S~:[~; actually ~:[uninterned~;~:*from ~S~]~] conflicts with existing symbol in ~S~:[~; actually ~:[uninterned~;from ~:*~S~]~]"
                    name (package-name from-package)
                    (home-package-p symbol from-package) (symbol-package-name symbol)
                    (package-name to-package)
                    (home-package-p existing to-package) (symbol-package-name existing)))
            (t
             (ensure-inherited name symbol to-package from-package t shadowed imported inherited)))))))

  (defun recycle-symbol (name recycle exported)
    ;; Takes a symbol NAME (a string), a list of package designators for RECYCLE
    ;; packages, and a hash-table of names (strings) of symbols scheduled to be
    ;; EXPORTED from the package being defined. It returns two values, the
    ;; symbol found (if any, or else NIL), and a boolean flag indicating whether
    ;; a symbol was found. The caller (DEFINE-PACKAGE) will then do the
    ;; re-homing of the symbol, etc.
    (check-type name string)
    (check-type recycle list)
    (check-type exported hash-table)
    (when (gethash name exported) ;; don't bother recycling private symbols
      (let (recycled foundp)
        (dolist (r recycle (values recycled foundp))
          (multiple-value-bind (symbol status) (find-symbol name r)
            (when (and status (home-package-p symbol r))
              (cond
                (foundp
                 ;; (nuke-symbol symbol)) -- even simple variable names like O or C will do that.
                 (note-package-fishiness :recycled-duplicate name (package-name foundp) (package-name r)))
                (t
                 (setf recycled symbol foundp r)))))))))
  (defun symbol-recycled-p (sym recycle)
    (check-type sym symbol)
    (check-type recycle list)
    (and (member (symbol-package sym) recycle) t))
  (defun ensure-symbol (name package intern recycle shadowed imported inherited exported)
    (check-type name string)
    (check-type package package)
    (check-type intern (member nil t)) ; no cl:boolean on Genera
    (check-type shadowed hash-table)
    (check-type imported hash-table)
    (check-type inherited hash-table)
    (unless (or (gethash name shadowed)
                (gethash name imported)
                (gethash name inherited))
      (multiple-value-bind (existing status)
          (find-symbol name package)
        (multiple-value-bind (recycled previous) (recycle-symbol name recycle exported)
          (cond
            ((and status (eq existing recycled) (eq previous package)))
            (previous
             (rehome-symbol recycled package))
            ((and status (eq package (symbol-package existing))))
            (t
             (when status
               (note-package-fishiness
                :ensure-symbol name
                (reify-package (symbol-package existing) package)
                status intern)
               (unintern existing))
             (when intern
               (intern* name package))))))))
  (declaim (ftype (function (t t t &optional t) t) ensure-exported))
  (defun ensure-exported-to-user (name symbol to-package &optional recycle)
    (check-type name string)
    (check-type symbol symbol)
    (check-type to-package package)
    (check-type recycle list)
    (assert (equal name (symbol-name symbol)))
    (multiple-value-bind (existing status) (find-symbol name to-package)
      (unless (and status (eq symbol existing))
        (let ((accessible
                (or (null status)
                    (let ((shadowing (symbol-shadowing-p existing to-package))
                          (recycled (symbol-recycled-p existing recycle)))
                      (unless (and shadowing (not recycled))
                        (note-package-fishiness
                         :ensure-export name (symbol-package-name symbol)
                         (package-name to-package)
                         (or (home-package-p existing to-package) (symbol-package-name existing))
                         status shadowing)
                        (if (or (eq status :inherited) shadowing)
                            (shadowing-import* symbol to-package)
                            (unintern existing to-package))
                        t)))))
          (when (and accessible (eq status :external))
            (ensure-exported name symbol to-package recycle))))))
  (defun ensure-exported (name symbol from-package &optional recycle)
    (dolist (to-package (package-used-by-list from-package))
      (ensure-exported-to-user name symbol to-package recycle))
    (unless (eq from-package (symbol-package symbol))
      (ensure-imported symbol from-package))
    (export* name from-package))
  (defun ensure-export (name from-package &optional recycle)
    (multiple-value-bind (symbol status) (find-symbol* name from-package)
      (unless (eq status :external)
        (ensure-exported name symbol from-package recycle))))

  #+package-local-nicknames
  (defun install-package-local-nicknames (destination-package new-nicknames)
    ;; First, remove all package-local nicknames. (We'll reinstall any desired ones later.)
    (dolist (pair-to-remove (uiop/package-local-nicknames:package-local-nicknames destination-package))
      (uiop/package-local-nicknames:remove-package-local-nickname
       (string (car pair-to-remove)) destination-package))
    ;; Then, install all desired nicknames.
    (loop :for (nickname package) :in new-nicknames
          :do (uiop/package-local-nicknames:add-package-local-nickname
               (string nickname)
               (find-package package)
               destination-package)))

  (defun ensure-package (name &key
                                nicknames documentation use
                                shadow shadowing-import-from
                                import-from export intern
                                recycle mix reexport
                                unintern local-nicknames)
    #+genera (declare (ignore documentation))
    (let* ((package-name (string name))
           (nicknames (mapcar #'string nicknames))
           (names (cons package-name nicknames))
           (previous (packages-from-names names))
           (discarded (cdr previous))
           (to-delete ())
           (package (or (first previous) (make-package package-name :nicknames nicknames)))
           (recycle (packages-from-names recycle))
           (use (mapcar 'find-package* use))
           (mix (mapcar 'find-package* mix))
           (reexport (mapcar 'find-package* reexport))
           (shadow (mapcar 'string shadow))
           (export (mapcar 'string export))
           (intern (mapcar 'string intern))
           (unintern (mapcar 'string unintern))
           (local-nicknames (mapcar #'(lambda (pair) (mapcar 'string pair)) local-nicknames))
           (shadowed (make-hash-table :test 'equal)) ; string to bool
           (imported (make-hash-table :test 'equal)) ; string to bool
           (exported (make-hash-table :test 'equal)) ; string to bool
           ;; string to list home package and use package:
           (inherited (make-hash-table :test 'equal)))
      #-package-local-nicknames
      (declare (ignore local-nicknames)) ; if not supported
      (when-package-fishiness (record-fishy package-name))
      ;; if supported, put package documentation
      #-genera
      (when documentation (setf (documentation package t) documentation))
      ;; remove unwanted packages from use list
      (loop :for p :in (set-difference (package-use-list package) (append mix use))
            :do (note-package-fishiness :over-use name (package-names p))
                (unuse-package p package))
      ;; mark unwanted packages for deletion
      (loop :for p :in discarded
            :for n = (remove-if #'(lambda (x) (member x names :test 'equal))
                                (package-names p))
            :do (note-package-fishiness :nickname name (package-names p))
                (cond (n (rename-package p (first n) (rest n)))
                      (t (rename-package-away p)
                         (push p to-delete))))
      ;; give package its desired name
      (rename-package package package-name nicknames)
      ;; Handle local nicknames
      #+package-local-nicknames
      (install-package-local-nicknames package local-nicknames)
      (dolist (name unintern)
        (multiple-value-bind (existing status) (find-symbol name package)
          (when status
            (unless (eq status :inherited)
              (note-package-fishiness
               :unintern (package-name package) name (symbol-package-name existing) status)
              (unintern* name package nil)))))
      ;; handle exports
      (dolist (name export)
        (setf (gethash name exported) t))
      ;; handle reexportss
      (dolist (p reexport)
        (do-external-symbols (sym p)
          (setf (gethash (string sym) exported) t)))
      ;; unexport symbols not listed in (re)export
      (do-external-symbols (sym package)
        (let ((name (symbol-name sym)))
          (unless (gethash name exported)
            (note-package-fishiness
             :over-export (package-name package) name
             (or (home-package-p sym package) (symbol-package-name sym)))
            (unexport sym package))))
      ;; handle explicitly listed shadowed ssymbols
      (dolist (name shadow)
        (setf (gethash name shadowed) t)
        (multiple-value-bind (existing status) (find-symbol name package)
          (multiple-value-bind (recycled previous) (recycle-symbol name recycle exported)
            (let ((shadowing (and status (symbol-shadowing-p existing package))))
              (cond
                ((eq previous package))
                (previous
                 (rehome-symbol recycled package))
                ((or (member status '(nil :inherited))
                     (home-package-p existing package)))
                (t
                 (let ((dummy (make-symbol name)))
                   (note-package-fishiness
                    :shadow-imported (package-name package) name
                    (symbol-package-name existing) status shadowing)
                   (shadowing-import* dummy package)
                   (import* dummy package)))))))
        (shadow* name package))
      ;; handle shadowing imports
      (loop :for (p . syms) :in shadowing-import-from
            :for pp = (find-package* p) :do
              (dolist (sym syms) (ensure-shadowing-import (string sym) package pp shadowed imported)))
      ;; handle mixed packages
      (loop :for p :in mix
            :for pp = (find-package* p) :do
              (do-external-symbols (sym pp) (ensure-mix (symbol-name sym) sym package pp shadowed imported inherited)))
      ;; handle import-from packages
      (loop :for (p . syms) :in import-from
            ;; FOR NOW suppress errors in the case where the :import-from
            ;; symbol list is empty (used only to establish a dependency by
            ;; package-inferred-system users).
            :for pp = (find-package* p syms) :do
              (when (null pp)
                ;; TODO: ASDF 3.4 Change to a full warning.
                (warn 'define-package-style-warning
                      :format-control "When defining package ~a, attempting to import-from non-existent package ~a. This is deprecated behavior and will be removed from UIOP in the future."
                      :format-arguments (list name p)))
              (dolist (sym syms) (ensure-import (symbol-name sym) package pp shadowed imported)))
      ;; handle use-list and mix
      (dolist (p (append use mix))
        (do-external-symbols (sym p) (ensure-inherited (string sym) sym package p nil shadowed imported inherited))
        (use-package p package))
      (loop :for name :being :the :hash-keys :of exported :do
        (ensure-symbol name package t recycle shadowed imported inherited exported)
        (ensure-export name package recycle))
      ;; intern dessired symbols
      (dolist (name intern)
        (ensure-symbol name package t recycle shadowed imported inherited exported))
      (do-symbols (sym package)
        (ensure-symbol (symbol-name sym) package nil recycle shadowed imported inherited exported))
      ;; delete now-deceased packages
      (map () 'delete-package* to-delete)
      package)))


(eval-when (:load-toplevel :compile-toplevel :execute)
  (defun parse-define-package-form (package clauses)
    (loop
      :with use-p = nil :with recycle-p = nil
      :with documentation = nil
      :for (kw . args) :in clauses
      :when (eq kw :nicknames) :append args :into nicknames :else
      :when (eq kw :documentation)
        :do (cond
              (documentation (error "define-package: can't define documentation twice"))
              ((or (atom args) (cdr args)) (error "define-package: bad documentation"))
              (t (setf documentation (car args)))) :else
      :when (eq kw :use) :append args :into use :and :do (setf use-p t) :else
      :when (eq kw :shadow) :append args :into shadow :else
      :when (eq kw :shadowing-import-from) :collect args :into shadowing-import-from :else
      :when (eq kw :import-from) :collect args :into import-from :else
      :when (eq kw :export) :append args :into export :else
      :when (eq kw :intern) :append args :into intern :else
      :when (eq kw :recycle) :append args :into recycle :and :do (setf recycle-p t) :else
      :when (eq kw :mix) :append args :into mix :else
      :when (eq kw :reexport) :append args :into reexport :else
      :when (eq kw :use-reexport) :append args :into use :and :append args :into reexport
        :and :do (setf use-p t) :else
      :when (eq kw :mix-reexport) :append args :into mix :and :append args :into reexport
        :and :do (setf use-p t) :else
      :when (eq kw :unintern) :append args :into unintern :else
      :when (eq kw :local-nicknames)
        :if (symbol-call '#:uiop '#:featurep :package-local-nicknames)
          :append args :into local-nicknames
        :else
          :do (error ":LOCAL-NICKAMES option is not supported on this lisp implementation.")
        :end
      :else
        :do (error "unrecognized define-package keyword ~S" kw)
      :finally (return `(',package
                         :nicknames ',nicknames :documentation ',documentation
                         :use ',(if use-p use '(:common-lisp))
                         :shadow ',shadow :shadowing-import-from ',shadowing-import-from
                         :import-from ',import-from :export ',export :intern ',intern
                         :recycle ',(if recycle-p recycle (cons package nicknames))
                         :mix ',mix :reexport ',reexport :unintern ',unintern
                         ,@(when local-nicknames
                             `(:local-nicknames ',local-nicknames)))))))

(defmacro define-package (package &rest clauses)
  "DEFINE-PACKAGE takes a PACKAGE and a number of CLAUSES, of the form
\(KEYWORD . ARGS\).
DEFINE-PACKAGE supports the following keywords:
SHADOW, SHADOWING-IMPORT-FROM, IMPORT-FROM, EXPORT, INTERN, NICKNAMES,
DOCUMENTATION -- as per CL:DEFPACKAGE.
USE -- as per CL:DEFPACKAGE, but if neither USE, USE-REEXPORT, MIX,
nor MIX-REEXPORT is supplied, then it is equivalent to specifying
(:USE :COMMON-LISP). This is unlike CL:DEFPACKAGE for which the
behavior of a form without USE is implementation-dependent.
RECYCLE -- Recycle the package's exported symbols from the specified packages,
in order.  For every symbol scheduled to be exported by the DEFINE-PACKAGE,
either through an :EXPORT option or a :REEXPORT option, if the symbol exists in
one of the :RECYCLE packages, the first such symbol is re-homed to the package
being defined.
For the sake of idempotence, it is important that the package being defined
should appear in first position if it already exists, and even if it doesn't,
ahead of any package that is not going to be deleted afterwards and never
created again. In short, except for special cases, always make it the first
package on the list if the list is not empty.
MIX -- Takes a list of package designators.  MIX behaves like
\(:USE PKG1 PKG2 ... PKGn\) but additionally uses :SHADOWING-IMPORT-FROM to
resolve conflicts in favor of the first found symbol.  It may still yield
an error if there is a conflict with an explicitly :IMPORT-FROM symbol.
REEXPORT -- Takes a list of package designators.  For each package, p, in the list,
export symbols with the same name as those exported from p.  Note that in the case
of shadowing, etc. the symbols with the same name may not be the same symbols.
UNINTERN -- Remove symbols here from PACKAGE. Note that this is primarily useful
when *redefining* a previously-existing package in the current image (e.g., when
upgrading ASDF).  Most programmers will have no use for this option.
LOCAL-NICKNAMES -- If the host implementation supports package local nicknames
\(check for the :PACKAGE-LOCAL-NICKNAMES feature\), then this should be a list of
nickname and package name pairs.  Using this option will cause an error if the
host CL implementation does not support it.
USE-REEXPORT, MIX-REEXPORT -- Use or mix the specified packages as per the USE or
MIX directives, and reexport their contents as per the REEXPORT directive."
  (let ((ensure-form
         `(prog1
              (funcall 'ensure-package ,@(parse-define-package-form package clauses))
            #+sbcl (setf (sb-impl::package-source-location (find-package ',package))
                         (sb-c:source-location)))))
    `(progn
       #+(or clasp ecl gcl mkcl) (defpackage ,package (:use))
       (eval-when (:compile-toplevel :load-toplevel :execute)
         ,ensure-form))))

;; This package, unlike UIOP/PACKAGE, is allowed to evolve and acquire new symbols or drop old ones.
(define-package :uiop/package*
  (:use-reexport :uiop/package
                 #+package-local-nicknames :uiop/package-local-nicknames)
  (:import-from :uiop/package
                #:define-package-style-warning
                #:no-such-package-error
                #:package-designator)
  (:export #:define-package-style-warning
           #:no-such-package-error
           #:package-designator))
