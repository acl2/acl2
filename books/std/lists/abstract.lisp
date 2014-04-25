; Base definitions of generic list predicates/projections/etc.
; Copyright (C) 2014 Centaur Technology Inc.
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc std/lists/abstract
  :parents (std/lists)
  :short "Abstract theories for listp, projection, and mapappend functions"
  :long "<p>This book defines various generic functions:</p>
<ul>
<li>element-p</li>
<li>element-fix</li>
<li>element-equiv</li>
<li>element-list-p</li>
<li>element-list-fix</li>
<li>element-list-equiv</li>
<li>element-list-projection</li>
<li>element-list-mapappend</li>
<ul>

<p>The idea is that in other books, we can add various theorems about how these
generic functions behave in relation to other functions such as nth, index-of,
member, etc, which we can use in pluggable forms of @(see deflist), @(see
defprojection), or @(see defmapappend).  However, this functionality isn't yet
implemented.</p>

<p>To collect theorems relating to list recognizers, projections, and mapappend
functions, we also define macros @(see def-listp-rule), @(see
def-projection-rule), and @(see def-mappapend-rule).  These are just like
defthm but additionally add the theorem name to a table so that later we can
use the rules in that table as a basis for extensible forms of deflist,
defprojection, and defmapappend.</p>")

(local (set-default-parents std/lists/abstract))



(defsection element-p
  :short "Generic typed list element recognizer.  Its only constraint is that
there must exist some element satisfying element-p."
  ;; Elementp functions for defining various types of list recognizers, with fixing functions.
  (encapsulate (((element-p *) => *)
                ((element-example) => *))

    (local (defun element-p (x) (natp x)))
    (local (defun element-example () 0))

    (defthm element-p-of-element-example
      (element-p (element-example)))))



(defsection element-fix
  :short "Generic fixing function for typed list elements."

  (encapsulate (((element-fix *) => *))

    (local (defun element-fix (x)
             (if (element-p x) x (element-example))))

    (defthm element-p-of-element-fix
      (element-p (element-fix x)))

    (defthm element-fix-when-element-p
      (implies (element-p x)
               (equal (element-fix x) x)))))

(defsection element-equiv
  :short "Generic equivalence relation among typed list elements."

  ;; (fty::deffixtype element :pred element-p :fix element-fix
  ;;   :equiv element-equiv :define t :forward t)
  (defun element-equiv (x y)
    (declare (xargs :verify-guards nil))
    (equal (element-fix x) (element-fix y)))

  (defequiv element-equiv)

  (defcong element-equiv equal (element-fix x) 1)

  (defthm element-fix-under-element-equiv
    (element-equiv (element-fix x) x))

  (defthm equal-of-element-fix-1-forward-to-element-equiv
    (implies (equal (element-fix x) y)
             (element-equiv x y))
    :rule-classes :forward-chaining)

  (defthm equal-of-element-fix-2-forward-to-element-equiv
    (implies (equal x (element-fix y))
             (element-equiv x y))
    :rule-classes :forward-chaining)

  (defthm element-equiv-of-element-fix-1-forward
    (implies (element-equiv (element-fix x) y)
             (element-equiv x y))
    :rule-classes :forward-chaining)

  (defthm element-equiv-of-element-fix-2-forward
    (implies (element-equiv x (element-fix y))
             (element-equiv x y))
    :rule-classes :forward-chaining))


;; (fty::deflist element-list :elt-type element)

(defsection element-list-p
  :short "Generic typed list recognizer function."

  (defun element-list-p (x)
    (if (atom x)
        (equal x nil)
      (and (element-p (car x))
           (element-list-p (cdr x)))))

  (defthm element-list-p-of-cons
    (equal (element-list-p (cons a x))
           (and (element-p a) (element-list-p x))))
  (defthm element-list-p-of-cdr
    (implies (element-list-p x)
             (element-list-p (cdr x))))
  (defthm element-p-car-of-element-list-p
    (implies (and (consp x) (element-list-p x))
             (element-p (car x)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))
  (defthm element-list-p-compound-recognizer
    (implies (element-list-p x)
             (or (consp x) (not x)))
    :rule-classes :compound-recognizer)

  (defthm element-list-p-of-append
    (implies (and (element-list-p a)
                  (element-list-p b))
             (element-list-p (append a b))))

  (defthm element-list-p-implies-true-listp
    (implies (element-list-p x)
             (true-listp x))
    :rule-classes :forward-chaining))

(defsection element-list-fix
  :short "Generic typed list fixing function."
  (defun element-list-fix (x)
    (if (atom x)
        nil
      (cons (element-fix (car x))
            (element-list-fix (cdr x)))))

  (defthm element-list-p-of-element-list-fix
    (element-list-p (element-list-fix x)))

  (defthm element-list-fix-when-element-list-p
    (implies (element-list-p x)
             (equal (element-list-fix x) x)))

  (defthm consp-of-element-list-fix
    (equal (consp (element-list-fix x))
           (consp x)))

  (defthm element-list-fix-of-cons
    (equal (element-list-fix (cons a x))
           (cons (element-fix a)
                 (element-list-fix x))))

  (defthm len-of-element-list-fix
    (equal (len (element-list-fix x))
           (len x)))

  (defthm element-fix-of-append
    (equal (element-list-fix (append a b))
           (append (element-list-fix a)
                   (element-list-fix b)))))


(defsection element-list-equiv
  :short "Generic typed list equivalence relation"
  (defun element-list-equiv (x y)
    (declare (xargs :verify-guards nil))
    (equal (element-list-fix x)
           (element-list-fix y)))

  (defequiv element-list-equiv)
  (defcong element-list-equiv equal (element-list-fix x) 1)
  (defthm element-list-fix-under-element-list-equiv
    (element-list-equiv (element-list-fix x)
                        x))
  (defthm equal-of-element-list-fix-1-forward-to-element-list-equiv
    (implies (equal (element-list-fix x) y)
             (element-list-equiv x y))
    :rule-classes :forward-chaining)
  (defthm equal-of-element-list-fix-2-forward-to-element-list-equiv
    (implies (equal x (element-list-fix y))
             (element-list-equiv x y))
    :rule-classes :forward-chaining)
  (defthm element-list-equiv-of-element-list-fix-1-forward
    (implies (element-list-equiv (element-list-fix x)
                                 y)
             (element-list-equiv x y))
    :rule-classes :forward-chaining)
  (defthm element-list-equiv-of-element-list-fix-2-forward
    (implies (element-list-equiv x (element-list-fix y))
             (element-list-equiv x y))
    :rule-classes :forward-chaining)

  (defcong element-list-equiv element-equiv (car x) 1)
  (defcong element-list-equiv element-list-equiv (cdr x) 1)
  (defcong element-equiv element-list-equiv (cons x y) 1)
  (defcong element-list-equiv element-list-equiv (cons x y) 2))



;; Another element type, for projections/mapappends
(defsection outelement-p
  :short "Generic recognizer for the output element type of a projection."
  (encapsulate
    (((outelement-p *) => *)
     ((outelement-example) => *))

    (local (defun outelement-p (x) (natp x)))
    (local (defun outelement-example () 0))

    (defthm outelement-p-of-outelement-example
      (outelement-p (outelement-example)))))

(defsection outelement-list-p
  :short "Generic recognizer for the output list type of a projection."

  (defun outelement-list-p (x)
    (if (atom x)
        (equal x nil)
      (and (outelement-p (car x))
           (outelement-list-p (cdr x)))))

  (defthm outelement-list-p-of-append
    (implies (and (outelement-list-p x)
                  (outelement-list-p y))
             (outelement-list-p (append x y)))))


(defsection element-xformer
  :short "Generic transform to be projected over a typed list."
  (encapsulate (((element-xformer *) => *))

    (local (defun element-xformer (x)
             (declare (ignore x))
             (outelement-example)))

    (defthm outelement-p-of-element-xformer
      (implies (element-p x)
               (outelement-p (element-xformer x))))))


(defsection elementlist-projection
  :short "Generic projection over a typed list."
  (defun elementlist-projection (x)
    (if (atom x)
        nil
      (cons (element-xformer (car x))
            (elementlist-projection (cdr x)))))

  (defthm outelement-list-p-of-elementlist-projection
    (implies (element-list-p x)
             (outelement-list-p (elementlist-projection x)))))



(defsection element-listxformer
  :short "Generic element->list transform for mapappend"
  
  (encapsulate (((element-listxformer *) => *))

    (local (defun element-listxformer (x)
             (declare (ignore x))
             (list (outelement-example))))

    (defthm outelement-list-p-of-element-listxformer
      (implies (element-p x)
               (outelement-list-p (element-listxformer x))))))


(defsection elementlist-mapappend
  :short "Generic mapappend over a typed list."
  (defun elementlist-mapappend (x)
    (if (atom x)
        nil
      (append (element-listxformer (car x))
              (elementlist-mapappend (cdr x)))))

  (defthm outelement-list-p-of-elementlist-mapappend
    (implies (element-list-p x)
             (outelement-list-p (elementlist-mapappend x)))))


(defun find-last-defthm (wrld)
  (declare (xargS :mode :program))
  (if (atom wrld)
      nil
    (if (and (eq (caar wrld) 'event-landmark)
             (eq (cadar wrld) 'global-value)
             (eq (access-event-tuple-type (cddar wrld)) 'defthm))
        (access-event-tuple-namex (cddar wrld))
      (find-last-defthm (cdr wrld)))))


(defsection def-projection-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about elementlist-projection."
  (defmacro def-projection-rule (name &rest args)
    `(progn (defthm ,name . ,args)
            (table projection-rules ',name t))))

(defsection def-listp-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about element-list-p."
  (defmacro def-listp-rule (name &rest args)
    `(progn (defthm ,name . ,args)
            (table listp-rules ',name t))))

(defsection def-listfix-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about element-list-fix."
  (defmacro def-listfix-rule (name &rest args)
    `(progn (defthm ,name . ,args)
            (table listfix-rules ',name t))))

(defsection def-mapappend-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about elementlist-mapappend."
  (defmacro def-mapappend-rule (name &rest args)
    `(progn (defthm ,name . ,args)
            (table mapappend-rules ',name t))))


(defsection add-projection-rule
  :short "Save the last defthm in a table, denoting that it is a rule about elementlist-projection."
  :long "<p>Note! Be careful when using this interactively.  E.g., if the
theorem you think you're targeting turns out to be redundant, then you'll add
the wrong rule.</p>"
  (defmacro add-projection-rule ()
    '(table projection-rules (find-last-defthm world) t)))

(defsection add-listp-rule
  :short "Save the last defthm in a table, denoting that it is a generic rule
pertaining to element-list-p."
  :long "<p>Note! Be careful when using this interactively.  E.g., if the
theorem you think you're targeting turns out to be redundant, then you'll add
the wrong rule.</p>"
  (defmacro add-listp-rule ()
    '(table listp-rules (find-last-defthm world) t)))

(defsection add-listfix-rule
  :short "Save the last defthm in a table, denoting that it is a generic rule
pertaining to element-list-fix."
  :long "<p>Note! Be careful when using this interactively.  E.g., if the
theorem you think you're targeting turns out to be redundant, then you'll add
the wrong rule.</p>"
  (defmacro add-listfix-rule ()
    '(table listfix-rules (find-last-defthm world) t)))

(defsection add-mapappend-rule
  :short "Save the last defthm in a table, denoting that it is a rule about elementlist-mapappend."
  :long "<p>Note! Be careful when using this interactively.  E.g., if the
theorem you think you're targeting turns out to be redundant, then you'll add
the wrong rule.</p>"
  (defmacro add-mapappend-rule ()
    '(table mapappend-rules (find-last-defthm world) t)))

