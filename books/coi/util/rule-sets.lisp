; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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


(in-package "ACL2")

(include-book "rule-sets-documentation")
(include-book "rule-sets-support")

(include-book "table")

;; Some suggestions for rule-sets that we should consider .. this
;; was in the file records/fixedpoint.lisp

;; So, table events can be made local.  This means that we can define:
;;
;; (activate-rule-sets a b c)
;;
;; and ..
;;
;; (globally-activate-rule-sets a b c)
;;
;; We could even have ..
;;
;; (finalize-rule-sets a b c)
;;
;; To prohbit additions to those rule sets in the future.
;;
;; for activations that we want to export.
;;
;; If a rule set is active, adding a rule to that set will
;; also enable that rule in your current world.
;;
;; If a rule set is inactive, adding a rule to that set will
;; disable that rule in your current world.

;; It would be nice to have an automated way to manage conflicts as
;; well.  For example, if you tried to enable a rule that conflicts
;; with another rule, it would disable the other rule.

;; ===================================================================
;; *rule-sets*:
;;
;; This is where the rule sets are stored in the ACL2 table.
;;
;; ===================================================================

(defconst *rule-sets* 'rule-sets)

;; ===================================================================
;;
;; def::rule-set :
;; def::library  :
;;
;; Used to define a new library or rule set.
;;
;; ===================================================================

(defmacro def::rule-set (name &key
			      (extends 'nil)
			      (omits 'nil))
  `(table::set *rule-sets* (rule-sets::define-new-set ',name ',extends ',omits (table::get *rule-sets* world))))

(defmacro def::library (&rest args)
  `(def::rule-set ,@args))

;; ===================================================================
;;
;; in-library:
;;
;; - Sets the default library/version to the one specified
;; - Sets the default version of the specified library.
;; - Transitions the theory state to reflect the new library.
;;
;; ===================================================================

(defmacro in-library (ref)
  (let ((version (if (consp ref) (cdr ref) nil)))
    `(local
      (progn
	(in-theory (set-difference-current-theory-fn
		    (rule-sets::ref-list-to-disable
		     (rule-sets::default-ref (table::get *rule-sets*))
		     (table::get *rule-sets*) nil)
		    nil world))
	(table::set
	 *rule-sets*
	 (rule-sets::set-ref-default-version-in-rule-set ',ref ',version
           (rule-sets::set-default-library ',ref (table::get *rule-sets* world))))
	(in-theory (rule-sets::d/e-list (current-theory :here)
					(rule-sets::ref-list-to-de ',ref (table::get *rule-sets*) nil) world))
	))))

;; ===================================================================
;;
;; set-library-version:
;;
;; - Sets the default version of the specified library.
;; - Transitions the theory state to reflect the new library.
;;
;; ===================================================================

(defmacro set-library-version (ref)
  `(make-event
    (let* ((ref     ',ref)
	   (key     (if (consp ref) (car ref) ref))
	   (version (if (consp ref) (cdr ref) nil))
	   (default (rule-sets::get-ref-default-version-in-rule-set ref (table::get *rule-sets* (w state))))
	   (oref    (cons key default)))
      (if (not (equal default version))
	  `(progn
	     (in-theory (set-difference-current-theory-fn
			 (rule-sets::ref-to-disable ',oref (table::get *rule-sets*) nil)
			 nil world))
	     (table::set
	      *rule-sets*
	      (rule-sets::set-ref-default-version-in-rule-set ',ref ',version (table::get *rule-sets* world))))
	'(table::set *rule-sets* (table::get *rule-sets* world))))))


;; ===================================================================
;;
;; classify-rule[s]:
;;
;; Allows a rule to be classified for multiple rule sets.
;;
;; ACL2 !> (classify-rule rule :enable (seta setb) :disable (set1 set2))
;;
;; ===================================================================

(defmacro classify-rule (rule &key (enable 'nil) (disable 'nil))
  `(table::set *rule-sets* (rule-sets::classify-rules '(,rule) ',enable ',disable (table::get *rule-sets* world))))

(defmacro classify-rules (rules &key (enable 'nil) (disable 'nil))
  `(table::set *rule-sets* (rule-sets::classify-rules ',rules ',enable ',disable (table::get *rule-sets* world))))

;; ===================================================================
;;
;; rule-set:
;;
;; We use this function to update a specific rule class with a list
;; of new new rules
;;
;; ACL2 !> (rule-set class-name rule1 rule2 ..)
;;
;; We can also use it to querry the state of a specific rule class:
;;
;; ACL2 !> (rule-set class-name)
;;
;; ===================================================================

(defmacro rule-set (name &rest rules)
  (if rules
      `(table::set
	*rule-sets*
	(rule-sets::add-rules-to-ref-in-rule-set ',name ',rules nil (table::get *rule-sets* world)))
    `(rule-sets::query-ref ',name (table::get *rule-sets* (w state)))))

;; ===================================================================
;;
;; rule-sets:
;;
;; Return the rule-sets database.
;;
;; ===================================================================

(defmacro rule-sets ()
  `(table::get *rule-sets* (w state)))

;; ===================================================================
;; eset:
;; dset:
;; e/d-set:
;;
;; These functions can be used to enable/disable entire rule classes.
;; The first argument is a theory expression and remaining arguments
;; are lists of rule sets.  These expressions can be nested in the
;; theory expression argument.  If the first argument is :here, these
;; macros behave like enable/disable or e/d.
;;
;; (in-theory (eset (dset :here class1) class2))
;;
;; ===================================================================

(defmacro eset (theory &rest list)
  `(rule-sets::d/e-list ,theory (rule-sets::ref-list-to-de '(,@list) (table::get *rule-sets*) nil) world))

(defmacro dset (theory &rest list)
  `(set-difference-theories-fn
    ,(if (equal theory :here) `(current-theory :here) theory)
    (rule-sets::ref-list-to-disable '(,@list) (table::get *rule-sets*) nil)
    t nil world))

(defmacro e/d-set (theory &rest list)
  `(rule-sets::d/e-list ,theory (rule-sets::alt-e/d-to-ed-list t '(,@list) (table::get *rule-sets*)) world))

;; ===================================================================
;;
;; Some simple tests and example applications.
;;
;; ===================================================================

(encapsulate
    ()
  (local
   (encapsulate
       ()

     (def::rule-set open-rules)
     (def::rule-set definitions)

     (defund foo (x) x)

     (defthmd open-foo
       (equal (foo x) x)
       :hints (("Goal" :in-theory (enable foo))))

     (rule-set open-rules open-foo)

     (defund goo (x) x)

     (defthmd open-goo
       (equal (goo x) x)
       :hints (("Goal" :in-theory (enable goo))))

     (rule-set open-rules open-goo)

     (defthmd foo-test-1
       (equal (foo x) (goo x))
       :hints (("Goal" :in-theory (eset :here open-rules))))

     (rule-set definitions foo goo)

     (defthmd foo-test-2
       (equal (foo x) (goo x))
       :hints (("Goal" :in-theory (eset (dset :here definitions)
					open-rules))))

     (defthmd foo-test-3
       (equal (foo x) (goo x))
       :hints (("Goal" :in-theory (e/d-set :here (open-rules) (definitions)))))

     ))
  )

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (encapsulate
	 ()

       (def::rule-set (frank . alpha))
       (def::rule-set joe)

       )

     (in-library (frank . alpha))

     (def::library (zed . beta)
       :extends ((frank . alpha))
       :omits (joe))

     (set-library-version (zed . beta))

     (classify-rule (:rewrite rule-name)
		    :enable   ((frank . alpha) joe)
		    :disable  ((zed . beta)))

     ))

  )
