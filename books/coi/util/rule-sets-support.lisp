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


(in-package "RULE-SETS")

;; ===================================================================
;;
;; The data structure used to hold the rule set state.
;;
;; ===================================================================

;; DAG - Should come from "lists"
(defthm true-listp-append-rewrite
  (equal (true-listp (append x y))
         (true-listp y)))

(defun wf-rule-list (list)
  (declare (type t list))
  (true-listp list))

(defthm wf-rule-list-implies-true-listp
  (implies
   (wf-rule-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

;; ===================================================================
;;
;; wf-set-ref: A reference to a rule set (or library).  It is either
;; an atom (just the name of the set) or a cons pair in which the
;; first atom is the name of the set and the second is the specific
;; version of that set.
;;
;; ===================================================================

(defun wf-set-ref (ref)
  (declare (type t ref))
  (or (eqlablep ref)
      (and (consp ref)
           (eqlablep (car ref))
           (eqlablep (cdr ref)))))

(defthm wf-set-ref-not-consp
  (implies
   (and
    (wf-set-ref ref)
    (not (consp ref)))
   (eqlablep ref))
  :rule-classes (:forward-chaining))

(defthm wf-set-ref-consp
  (implies
   (and
    (wf-set-ref ref)
    (consp ref))
   (and (eqlablep (car ref))
        (eqlablep (cdr ref))))
  :rule-classes (:forward-chaining))

(defthm wf-set-ref-deduction-1
  (implies
   (and
    (consp ref)
    (eqlablep (car ref))
    (eqlablep (cdr ref)))
   (wf-set-ref ref))
  :rule-classes (:rewrite :forward-chaining))

(defthm wf-set-ref-deduction-2
  (implies
   (eqlablep ref)
   (wf-set-ref ref))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable wf-set-ref))

;; ===================================================================
;;
;; wf-set-ref-list: list[wf-set-ref]
;;
;; ===================================================================

(defun wf-set-ref-list (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-set-ref (car list))
           (wf-set-ref-list (cdr list)))
    (null list)))

(defthm wf-set-ref-list-append
  (implies
   (true-listp x)
   (equal (wf-set-ref-list (append x y))
          (and (wf-set-ref-list x)
               (wf-set-ref-list y)))))

(defthm wf-set-ref-list-implies-true-listp
  (implies
   (wf-set-ref-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

;; ===================================================================
;;
;; A version entry data structure
;;
;; version-entry: [
;;   version: eqlablep
;;   include-rules : wf-rule-list
;;   omit-rules    : wf-rule-list
;;   include-sets  : wf-set-ref-list
;;   omit-sets     : wf-set-ref-list
;; ]
;;
;; ===================================================================

(defun weak-version-entry (entry)
  (declare (type t entry))
  (and (true-listp entry)
       (equal (len entry) 5)))

(defun versi0n (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (car entry))

(defun include-rules (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (cadr entry))

(defun omit-rules (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (caddr entry))

(defun include-sets (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (cadddr entry))

(defun omit-sets (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (car (cddddr entry)))

(defun wf-version-entry (entry)
  (declare (type t entry))
  (and (weak-version-entry entry)
       (eqlablep (versi0n entry))
       (wf-rule-list (include-rules entry))
       (wf-rule-list (omit-rules entry))
       (wf-set-ref-list (include-sets entry))
       (wf-set-ref-list (omit-sets entry))))

(defthm wf-version-entry-implications
  (implies
   (wf-version-entry entry)
   (and (weak-version-entry entry)
        (eqlablep (versi0n entry))
        (wf-rule-list (include-rules entry))
        (wf-rule-list (omit-rules entry))
        (wf-set-ref-list (include-sets entry))
        (wf-set-ref-list (omit-sets entry))))
  :rule-classes (:forward-chaining))

(defthm wf-version-entry-deduction-implicit
  (implies
   (and (weak-version-entry entry)
        (eqlablep (versi0n entry))
        (wf-rule-list (include-rules entry))
        (wf-rule-list (omit-rules entry))
        (wf-set-ref-list (include-sets entry))
        (wf-set-ref-list (omit-sets entry)))
   (wf-version-entry entry))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((wf-version-entry entry)))))

(defun version-entry (versi0n include-rules omit-rules include-sets omit-sets)
  (declare (type (satisfies eqlablep) versi0n)
           (type (satisfies wf-rule-list) include-rules omit-rules)
           (type (satisfies wf-set-ref-list) include-sets omit-sets))
  (list versi0n include-rules omit-rules include-sets omit-sets))

(defthm version-entry-is-weak-version-entry
  (weak-version-entry (version-entry versi0n include-rules omit-rules include-sets omit-sets))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((version-entry versi0n include-rules omit-rules include-sets omit-sets)))))


(defthm version-entry-accessor-of-constructor
  (and
   (equal (versi0n (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          versi0n)
   (equal (include-rules (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          include-rules)
   (equal (omit-rules (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          omit-rules)
   (equal (include-sets (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          include-sets)
   (equal (omit-sets (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          omit-sets)))

(defthm wf-version-entry-deduction-explicit
  (implies
   (and (eqlablep versi0n)
        (wf-rule-list include-rules)
        (wf-rule-list omit-rules)
        (wf-set-ref-list include-sets)
        (wf-set-ref-list omit-sets))
   (wf-version-entry (version-entry versi0n include-rules omit-rules include-sets omit-sets)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((version-entry versi0n include-rules omit-rules include-sets omit-sets)))))

(in-theory (disable wf-version-entry weak-version-entry version-entry))
(in-theory (disable versi0n include-rules omit-rules include-sets omit-sets))

(defmacro new-version-entry (&key
                             (version 'nil)
                             (include-rules 'nil)
                             (omit-rules 'nil)
                             (include-sets 'nil)
                             (omit-sets 'nil))
  `(version-entry ,version ,include-rules ,omit-rules ,include-sets ,omit-sets))

(defmacro update-version-entry (set &key
                                    (version 'nil)
                                    (include-rules 'nil)
                                    (omit-rules 'nil)
                                    (include-sets 'nil)
                                    (omit-sets 'nil))
  (let ((version       (or version `(versi0n ,set)))
        (include-rules (or include-rules `(include-rules ,set)))
        (omit-rules    (or omit-rules `(omit-rules ,set)))
        (include-sets  (or include-sets `(include-sets ,set)))
        (omit-sets     (or omit-sets `(omit-sets ,set))))
    `(version-entry ,version ,include-rules ,omit-rules ,include-sets ,omit-sets)))

;; ===================================================================
;;
;; wf-version-list: list[wf-version-entry]
;;
;; ===================================================================

(defun wf-version-list (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-version-entry (car list))
           (wf-version-list (cdr list)))
    (null list)))

(defthm wf-version-list-implies-true-listp
  (implies
   (wf-version-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defun contains-version-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-version-list) list))
  (if (consp list)
      (or (equal set (versi0n (car list)))
          (contains-version-entry set (cdr list)))
    nil))

(defun get-version-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-version-list) list))
  (if (consp list)
      (if (equal set (versi0n (car list)))
          (car list)
        (get-version-entry set (cdr list)))
    (new-version-entry :version set)))

(defthm wf-version-entry-get-version-entry
  (implies
   (and
    (wf-version-list list)
    (eqlablep set))
   (wf-version-entry (get-version-entry set list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((get-version-entry set list)))))

(defun set-version-entry (set entry list)
  (declare (type (satisfies wf-version-list) list)
           (type (satisfies eqlablep) set)
           (type (satisfies wf-version-entry) entry))
  (if (consp list)
      (if (equal set (versi0n (car list)))
          (cons entry (cdr list))
        (cons (car list) (set-version-entry set entry (cdr list))))
    (list entry)))

(defthm wf-version-list-set-version-entry
  (implies
   (and
    (wf-version-entry entry)
    (wf-version-list list))
   (wf-version-list (set-version-entry set entry list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((set-version-entry set entry list)))))

;; ===================================================================
;;
;; A rule set entry data structure
;;
;; rule-set-entry : [
;;   set-name: eqlablep
;;   default-set-version: eqlablep
;;   version-list: wf-version-list
;; ]
;;
;; ===================================================================

(defun weak-rule-set-entry (entry)
  (declare (type t entry))
  (and (true-listp entry)
       (equal (len entry) 3)))

(defun set-name (entry)
  (declare (type (satisfies weak-rule-set-entry) entry))
  (car entry))

(defun default-set-version (entry)
  (declare (type (satisfies weak-rule-set-entry) entry))
  (cadr entry))

(defun version-list (entry)
  (declare (type (satisfies weak-rule-set-entry) entry))
  (caddr entry))

(defun wf-rule-set-entry (entry)
  (declare (type t entry))
  (and (weak-rule-set-entry entry)
       (eqlablep (set-name entry))
       (eqlablep (default-set-version entry))
       (wf-version-list (version-list entry))))

(defthm wf-rule-set-entry-implications
  (implies
   (wf-rule-set-entry entry)
   (and (weak-rule-set-entry entry)
        (eqlablep (set-name entry))
        (eqlablep (default-set-version entry))
       (wf-version-list (version-list entry))))
  :rule-classes (:forward-chaining))

(defthm wf-rule-set-entry-deduction-implicit
  (implies
   (and (weak-rule-set-entry entry)
        (eqlablep (set-name entry))
        (eqlablep (default-set-version entry))
       (wf-version-list (version-list entry)))
   (wf-rule-set-entry entry))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((wf-rule-set-entry entry)))))

(defun rule-set-entry (set-name default-set-version version-list)
  (declare (type (satisfies eqlablep) set-name default-set-version)
           (type (satisfies wf-version-list) version-list))
  (list set-name default-set-version version-list))

(defthm rule-set-entry-is-weak-rule-set-entry
  (weak-rule-set-entry (rule-set-entry set-name default-set-version version-list))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((rule-set-entry set-name default-set-version version-list)))))


(defthm rule-set-entry-accessor-of-constructor
  (and
   (equal (set-name (rule-set-entry set-name default-set-version version-list))
          set-name)
   (equal (default-set-version (rule-set-entry set-name default-set-version version-list))
          default-set-version)
   (equal (version-list (rule-set-entry set-name default-set-version version-list))
          version-list)))

(defthm wf-rule-set-entry-deduction-explicit
  (implies
   (and (eqlablep set-name)
        (eqlablep default-set-version)
        (wf-version-list version-list))
   (wf-rule-set-entry (rule-set-entry set-name default-set-version version-list)))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((rule-set-entry set-name default-set-version version-list)))))

(in-theory (disable wf-rule-set-entry weak-rule-set-entry rule-set-entry))
(in-theory (disable set-name default-set-version version-list))

(defmacro new-rule-set-entry (&key (set-name 'nil)
                                   (default-set-version 'nil)
                                   (version-list 'nil))
  `(rule-set-entry ,set-name ,default-set-version ,version-list))

(defmacro update-rule-set-entry (set &key
                                     (set-name 'nil)
                                     (default-set-version 'nil)
                                     (version-list 'nil))
  (let ((set-name (or set-name `(set-name ,set)))
        (default-set-version (or default-set-version `(default-set-version ,set)))
        (version-list (or version-list `(version-list ,set))))
    `(rule-set-entry ,set-name ,default-set-version ,version-list)))

;; ===================================================================
;;
;; wf-rule-set-list: list[wf-rule-set-entry]
;;
;; ===================================================================

(defun wf-rule-set-list (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-rule-set-entry (car list))
           (wf-rule-set-list (cdr list)))
    (null list)))

(defthm wf-rule-set-list-implies-true-listp
  (implies
   (wf-rule-set-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defun contains-rule-set-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-rule-set-list) list))
  (if (consp list)
      (or (equal set (set-name (car list)))
          (contains-rule-set-entry set (cdr list)))
    nil))

(defun get-rule-set-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-rule-set-list) list))
  (if (consp list)
      (if (equal set (set-name (car list)))
          (car list)
        (get-rule-set-entry set (cdr list)))
    (new-rule-set-entry :set-name set)))

(defthm wf-rule-set-entry-get-rule-set-entry
  (implies
   (and
    (wf-rule-set-list list)
    (eqlablep set))
   (wf-rule-set-entry (get-rule-set-entry set list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((get-rule-set-entry set list)))))

(defun set-rule-set-entry (set entry list)
  (declare (type (satisfies wf-rule-set-list) list)
           (type (satisfies eqlablep) set)
           (type (satisfies wf-rule-set-entry) entry))
  (if (consp list)
      (if (equal set (set-name (car list)))
          (cons entry (cdr list))
        (cons (car list) (set-rule-set-entry set entry (cdr list))))
    (list entry)))

(defthm wf-rule-set-list-set-rule-set-entry
  (implies
   (and
    (wf-rule-set-entry entry)
    (wf-rule-set-list list))
   (wf-rule-set-list (set-rule-set-entry set entry list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((set-rule-set-entry set entry list)))))

;; ===================================================================
;;
;; The rule set data structure
;;
;; rule-set: [
;;  default-library : eqlablep
;;  default-version : eqlablep
;;  rule-set-list   : wf-rule-set-list
;; ]
;;
;; ===================================================================

(defun weak-rule-set (set)
  (declare (type t set))
  (and (true-listp set)
       (equal (len set) 3)))

(defun default-library (rule-set)
  (declare (type (satisfies weak-rule-set) rule-set))
  (car rule-set))

(defun default-version (rule-set)
  (declare (type (satisfies weak-rule-set) rule-set))
  (cadr rule-set))

(defun rule-set-list (rule-set)
  (declare (type (satisfies weak-rule-set) rule-set))
  (caddr rule-set))

(defun wf-rule-set (set)
  (declare (type t set))
  (and (weak-rule-set set)
       (eqlablep (default-library set))
       (eqlablep (default-version set))
       (wf-rule-set-list (rule-set-list set))))

(defthm wf-rule-set-implications
  (implies
   (wf-rule-set set)
   (and (weak-rule-set set)
        (eqlablep (default-library set))
        (eqlablep (default-version set))
        (wf-rule-set-list (rule-set-list set))))
  :rule-classes (:forward-chaining))

(defthm wf-rule-set-deduction-implicit
  (implies
   (and (weak-rule-set set)
        (eqlablep (default-library set))
        (eqlablep (default-version set))
        (wf-rule-set-list (rule-set-list set)))
   (wf-rule-set set))
  :rule-classes (:rewrite :forward-chaining))


;; Constructor
;;
(defun rule-set (default-library default-version rule-set-list)
  (declare (type (satisfies eqlablep) default-library)
           (type (satisfies eqlablep) default-version)
           (type (satisfies wf-rule-set-list) rule-set-list))
  (list default-library default-version rule-set-list))

(defthm rule-set-is-weak-rule-set
  (weak-rule-set (rule-set default-library default-version rule-set-list))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((rule-set default-library default-version rule-set-list)))))

(defthm rule-set-accessor-of-constructor
  (and
   (equal (default-library (rule-set default-library default-version rule-set-list))
          default-library)
   (equal (default-version (rule-set default-library default-version rule-set-list))
          default-version)
   (equal (rule-set-list (rule-set default-library default-version rule-set-list))
          rule-set-list)))

(defthm wf-rule-set-deduction-explicit
  (implies
   (and (eqlablep default-library)
        (eqlablep default-version)
        (wf-rule-set-list rule-set-list))
   (wf-rule-set (rule-set default-library default-version rule-set-list)))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((rule-set default-library default-version rule-set-list)))))

(in-theory (disable wf-rule-set weak-rule-set rule-set))
(in-theory (disable default-library default-version rule-set-list))

(defmacro new-rule-set (&key (default-library 'nil)
                             (default-version 'nil)
                             (rule-set-list   'nil))
  `(rule-set ,default-library ,default-version ,rule-set-list))

(defmacro update-rule-set (set &key
                               (default-library 'nil)
                               (default-version 'nil)
                               (rule-set-list 'nil))
  (let ((default-library (or default-library `(default-library ,set)))
        (default-version (or default-version `(default-version ,set)))
        (rule-set-list   (or rule-set-list `(rule-set-list ,set))))
    `(rule-set ,default-library ,default-version ,rule-set-list)))

;; ===================================================================
;;
;; Utility functions for manipulating the rule-set data structure
;;
;; ===================================================================

(defun assert (value test ctx msg)
  (declare (type t ctx msg))
  (prog2$ (if (not test) (acl2::hard-error ctx "~p0" (list (cons #\0 msg))) nil)
	  value))

(defun ref-exists (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
	   (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list (rule-set-list rule-set))
	 (key            (if (consp ref) (car ref) ref))
	 (rule-set-exits (contains-rule-set-entry key rule-set-list))
	 (rule-set-entry (get-rule-set-entry key rule-set-list))
	 (version-list   (version-list rule-set-entry))
	 (version        (if (consp ref) (cdr ref) nil))
	 (version-exists (contains-version-entry version version-list)))
    (and rule-set-exits
	 version-exists)))

(defun ref-set-exists (list rule-set)
  (declare (type (satisfies wf-rule-set) rule-set)
	   (type (satisfies wf-set-ref-list) list))
  (if (consp list)
      (let ((ref (car list)))
	(and (ref-exists ref rule-set)
	     (ref-set-exists (cdr list) rule-set)))
    t))

;; ===================================================================
;; add-rules-to-ref-in-rule-set
;; ===================================================================

(defun add-rules-to-ref-in-rule-set (ref include-rules omit-rules rule-set)
  (declare (type (satisfies wf-set-ref) ref)
	   (type (satisfies wf-rule-list) include-rules omit-rules)
	   (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set       (assert rule-set (not (null rule-set))
				 'add-rules-to-ref-in-rule-set "Not rule-sets defined"))
	 (ref            (assert ref (ref-exists ref rule-set)
				 'add-rules-to-ref-in-rule-set "Undefined rule-set reference"))
	 (rule-set-list  (rule-set-list rule-set))
	 (key            (if (consp ref) (car ref) ref))
	 (rule-set-entry (get-rule-set-entry key rule-set-list))
	 (version-list   (version-list rule-set-entry))
	 (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
	 (version-entry  (get-version-entry version version-list))
	 (version-entry  (update-version-entry version-entry
					       :include-rules (append include-rules
								      (include-rules version-entry))
					       :omit-rules (append omit-rules
								   (omit-rules version-entry))))
	 (version-list   (set-version-entry version version-entry version-list))
	 (rule-set-entry (update-rule-set-entry rule-set-entry
						:version-list version-list))
	 (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

(defthm wf-rule-set-add-rules-to-ref-in-rule-set
  (implies
   (and
    (wf-set-ref ref)
    (wf-rule-list include-rules)
    (wf-rule-list omit-rules)
    (wf-rule-set rule-set))
   (wf-rule-set (add-rules-to-ref-in-rule-set ref include-rules omit-rules rule-set)))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms
		  ((add-rules-to-ref-in-rule-set ref include-rules omit-rules rule-set)))))

(in-theory (disable add-rules-to-ref-in-rule-set))

;; ===================================================================
;; add-rules-to-include-set
;; ===================================================================

(defun add-rules-to-include-set (rules include rule-set)
  (declare (type (satisfies wf-rule-set) rule-set)
	   (type (satisfies wf-rule-list) rules)
	   (type (satisfies wf-set-ref-list) include))
  (if (consp include)
      (let ((ref (car include)))
	(let ((rule-set (add-rules-to-ref-in-rule-set ref rules nil rule-set)))
	  (add-rules-to-include-set rules (cdr include) rule-set)))
    rule-set))

(defthm wf-rule-set-add-rules-to-include-set
  (implies
   (and (wf-rule-set rule-set)
	(wf-rule-list rules)
	(wf-set-ref-list include))
   (wf-rule-set (add-rules-to-include-set rules include rule-set))))

;; ===================================================================
;; add-rules-to-omit-set
;; ===================================================================

(defun add-rules-to-omit-set (rules omit rule-set)
  (declare (type (satisfies wf-rule-set) rule-set)
	   (type (satisfies wf-rule-list) rules)
	   (type (satisfies wf-set-ref-list) omit))
  (if (consp omit)
      (let ((ref (car omit)))
	(let ((rule-set (add-rules-to-ref-in-rule-set ref nil rules rule-set)))
	  (add-rules-to-omit-set rules (cdr omit) rule-set)))
    rule-set))

(defthm wf-rule-set-add-rules-to-omit-set
  (implies
   (and (wf-rule-set rule-set)
	(wf-rule-list rules)
	(wf-set-ref-list omit))
   (wf-rule-set (add-rules-to-omit-set rules omit rule-set))))

;; ===================================================================
;; add-sets-to-ref-in-rule-set
;; ===================================================================

;; o Check to make sure that all of the sets being
;;   added actually exist before we call this.

(defun add-sets-to-ref-in-rule-set (ref include-sets omit-sets rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-set-ref-list) include-sets omit-sets)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (version-list   (version-list rule-set-entry))
         (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
         (version-entry  (get-version-entry version version-list))
         (version-entry  (update-version-entry version-entry
                                               :include-sets (append include-sets
                                                                      (include-sets version-entry))
                                               :omit-sets (append omit-sets
                                                                   (omit-sets version-entry))))
         (version-list   (set-version-entry version version-entry version-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :version-list version-list))
         (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

(defthm wf-rule-set-add-sets-to-ref-in-rule-set
  (implies
   (and
    (wf-set-ref ref)
    (wf-set-ref-list include-sets)
    (wf-set-ref-list omit-sets)
    (wf-rule-set rule-set))
   (wf-rule-set (add-sets-to-ref-in-rule-set ref include-sets omit-sets rule-set)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((add-sets-to-ref-in-rule-set ref include-sets omit-sets rule-set)))))

(in-theory (disable add-sets-to-ref-in-rule-set))

;; ===================================================================
;; set-ref-default-version-in-rule-set
;; ===================================================================

(defun set-ref-default-version-in-rule-set (ref version rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies eqlablep) version)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :default-set-version version))
         (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

(defun get-ref-default-version-in-rule-set (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
	   (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
	 (key            (if (consp ref) (car ref) ref))
	 (rule-set-entry (get-rule-set-entry key rule-set-list)))
    (default-set-version rule-set-entry)))

;; ===================================================================
;; set-default-library
;; ===================================================================

(defun set-default-library (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((key            (if (consp ref) (car ref) ref))
	 (version        (if (consp ref) (cdr ref) nil)))
    (let ((rule-set (assert rule-set (ref-exists (cons key version) rule-set)
			    'set-default-library "Undefined rule-set reference")))
      (update-rule-set rule-set
		       :default-library key
		       :default-version version))))



;; ===================================================================
;; default-ref
;; ===================================================================

(defun default-ref (rule-set)
  (declare (type (satisfies wf-rule-set) rule-set))
  (if (default-version rule-set)
      (cons (default-library rule-set)
	    (default-version rule-set))
    (default-library rule-set)))

;; ===================================================================
;; d/e list:
;;
;;   A list containing pairs of lists.  The first list in a given pair
;; is the disable set, the second is an enable set.
;;
;; The following functions are all in :program mode because we don't
;; have a guarantee (don't care to ensure) that they terminate ..
;; although we do what we can in the construction of the rule-set data
;; structure to ensure that they will.
;;
;; ref-to-de:
;;
;;   Computes a d/e list from a reference
;;
;; ref-to-disable:
;;
;;   Computes a disable list from a reference
;;
;; ref-list-to-de:
;;
;;   Maps ref-to-de over a list of references.
;;
;; ref-list-to-disable:
;;
;;   Maps ref-to-disable over a list of references.
;;
;; ===================================================================

(mutual-recursion

 (defun ref-list-to-disable (list rule-set disable)
   (if (consp list)
       (let ((disable (ref-to-disable (car list) rule-set disable)))
         (ref-list-to-disable (cdr list) rule-set disable))
     disable))

 (defun ref-to-disable (ref rule-set disable)
   (let* ((rule-set-list  (rule-set-list rule-set))
          (key            (if (consp ref) (car ref) ref))
          (rule-set-entry (get-rule-set-entry key rule-set-list))
          (version-list   (version-list rule-set-entry))
          (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
          (version-entry  (get-version-entry version version-list))
          ;;
          ;; Is there any reason to include the omit-rules here, too?
          ;;
          (disable        (append (include-rules version-entry) disable)))
     (ref-list-to-disable (include-sets version-entry) rule-set disable)))

 (defun ref-list-to-de (list rule-set res)
   (declare (xargs :mode :program))
   (if (consp list)
       (let ((res (ref-to-de (car list) rule-set res)))
         (ref-list-to-de (cdr list) rule-set res))
     res))

 (defun ref-to-de (ref rule-set res)
   (declare (xargs :mode :program))
   (let* ((rule-set-list  (rule-set-list rule-set))
	  (key            (if (consp ref) (car ref) ref))
	  (rule-set-entry (get-rule-set-entry key rule-set-list))
	  (version-list   (version-list rule-set-entry))
	  (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
	  (version-entry  (get-version-entry version version-list))
	  ;;
	  ;; Delta accounts for versions which are not the default
	  ;; (currently active) versions of these libraries by
	  ;; first disabling the currently active versions.
	  ;;
	  (delta          (and (consp ref)
			       (not (equal version (default-set-version rule-set-entry)))
			       (ref-to-disable (cons (car ref) (default-set-version rule-set-entry)) rule-set nil)))
	  (res            (cons (cons (append delta (omit-rules version-entry))
				      (include-rules version-entry))
				res))
	  (res            (cons (list (ref-list-to-disable (omit-sets version-entry) rule-set nil))
				res)))
     (ref-list-to-de (include-sets version-entry) rule-set res)))

 )

(defun define-new-set (ref extends omits rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-set-ref-list) extends omits)
           (xargs :guard (or (null rule-set)
                             (wf-rule-set rule-set))))
  (let* ((rule-set       (or rule-set (new-rule-set)))
	 (rule-set       (assert rule-set (and (ref-set-exists extends rule-set)
					       (ref-set-exists omits   rule-set))
				 'define-new-set "All extended/omitted rule sets must already exist"))
	 (rule-set-list  (rule-set-list rule-set))
	 (key            (if (consp ref) (car ref) ref))
	 (version        (if (consp ref) (cdr ref) nil))

	 (rule-set-entry (get-rule-set-entry key rule-set-list))
	 (default-set-version (if (contains-rule-set-entry key rule-set-list)
				  (default-set-version rule-set-entry)
				version))
	 (rule-set-entry (update-rule-set-entry rule-set-entry
						:default-set-version default-set-version))
	 (version-list   (version-list rule-set-entry))
	 (version-entry  (get-version-entry version version-list))
	 (include-sets   (include-sets version-entry))
	 (omit-sets      (omit-sets version-entry))
	 (version-entry  (assert version-entry (or
						(not (contains-version-entry version version-list))
						(and (equal omit-sets omits)
						     (equal include-sets extends)))
				 'define-new-set "Fundamental redefinition of rule-classes is prohibited"))
	 (version-entry  (update-version-entry version-entry
					       :include-sets extends
					       :omit-sets omits))
	 (version-list   (set-version-entry version version-entry version-list))
	 (rule-set-entry (update-rule-set-entry rule-set-entry
						:version-list version-list))
	 (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

;;
;;
;;

(defun classify-rules (rules include exclude rule-set)
  (declare (type (satisfies wf-rule-set) rule-set)
	   (type (satisfies wf-rule-list) rules)
	   (type (satisfies wf-set-ref-list) include exclude))
  (let ((default-library (default-library rule-set))
	(default-version (default-version rule-set)))
    (let ((include (if (or default-library default-version)
		       (cons (cons default-library default-version)
			     include)
		     include)))
      (let ((rule-set (add-rules-to-include-set rules include rule-set)))
	(add-rules-to-omit-set rules exclude rule-set)))))

(defun query-ref (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list)))
    (if (consp ref)
        (let* ((version        (cdr ref))
               (version-list   (version-list rule-set-entry)))
          (get-version-entry version version-list))
      rule-set-entry)))

(defun alt-e/d-to-ed-list (e list rule-set)
  (declare (xargs :mode :program))
  (if (consp list)
      (append (if e (ref-list-to-de (car list) rule-set nil)
                (list (list (ref-list-to-disable (car list) rule-set nil))))
              (alt-e/d-to-ed-list (not e) (cdr list) rule-set))
    nil))

(defun d/e-list (theory list world)
  (declare (xargs :mode :program))
  (if (consp list)
      (let ((disable (caar list))
            (enable  (cdar list)))
        (acl2::union-theories-fn
         (acl2::set-difference-theories-fn
          (d/e-list theory (cdr list) world)
          disable
          t nil world)
         enable
         t world))
    (if (equal theory :here) (current-theory :here) (acl2::RUNIC-THEORY theory WORLD))))

#|

  o First, implement the exising rule set infrastructure with this as
an underpinning.

  o Add additional versioning capabilities as permitted.

;; Associated with each version are:
;; - the classes to disable
;; - the classes to enable
;; - the rules to disable
;; - the rules to enable

;; - may not redefine (change) a version extension.
;; - must be defined in terms of an existing version.
;; - by default, a version extends nil (the initial version)

(defun update-library-version (new old list)
  (let ((hit (assoc new list)))
    (if (consp hit)
        (if (equal (cdr hit) old) list
          (error "Cannot Redefine"))
      (cons (cons new old) list))))

;; If we need to change "active" versions,
;; - back out of the current version
;; - enstate the new version

;; modifies the current version of a specified library
;;
(set-current-version library/class version)

(new-library-version name version)

(define-version library/class
  :version new-version-name
  :extends old-version-name)

(incompatible-rule-sets set1 set2)

(rule-set-extension :base set1 :extension set2)


(include-set-extension-with-base-set base extension)
(omit-set-from-base-set base omission)

;;
;; Perhaps class relations are established only during definition.
;;

(new-rule-set name
              :extends ..
              :omits ..)

(add-rules-to-set set names)
(omit-rules-from-set set names)

:rule-sets (x y z)
:omit-sets (p d q)

|#
