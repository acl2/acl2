; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "centaur/meta/parse-rewrite" :dir :system)
(include-book "std/util/defenum" :dir :system)
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable pseudo-termp
                           pseudo-term-listp
                           acl2::pseudo-termp-opener)))



(std::defenum fgl-rule-arg-mode-p (:bound :either :unbound))

(fty::deflist fgl-rule-arg-mode-list :elt-type fgl-rule-arg-mode-p
  :true-listp t)

(fty::defflexsum fgl-rune
  :short "A rule identifier, including an optional ACL2 rune index."
  :long "<p>Rewrite and definition runes use ACL2's representation
@('(:rewrite name . index)') or @('(:definition name . index)'), where the
index is NIL or a positive integer. Other kinds have the form @('(kind name)').</p>"
  (:rewrite
   :cond (and (consp x) (eq (car x) :rewrite))
   :shape (and (consp x) (consp (cdr x)))
   :fields ((name :acc-body (cadr x))
            (index :type acl2::maybe-posp :acc-body (cddr x)))
   :ctor-body (list* :rewrite name index))
  (:definition
   :cond (and (consp x) (eq (car x) :definition))
   :shape (and (consp x) (consp (cdr x)))
   :fields ((name :acc-body (cadr x))
            (index :type acl2::maybe-posp :acc-body (cddr x)))
   :ctor-body (list* :definition name index))
  (:formula
   :cond (and (consp x) (eq (car x) :formula))
   :shape (and (consp x) (consp (cdr x)) (not (cddr x)))
   :fields ((name :type pseudo-fnsym-p :acc-body (cadr x)))
   :ctor-body (list :formula name))
  (:primitive
   :cond (and (consp x) (eq (car x) :primitive))
   :shape (and (consp x) (consp (cdr x)) (not (cddr x)))
   :fields ((name :type pseudo-fnsym-p :acc-body (cadr x)))
   :ctor-body (list :primitive name))
  (:meta
   :shape (and (consp x) (eq (car x) :meta)
               (consp (cdr x)) (not (cddr x)))
   :fields ((name :type pseudo-fnsym-p :acc-body (cadr x)))
   :ctor-body (list :meta name)))

(fty::defprod fgl-ruledata
  ((rune fgl-rune-p)
   (prio integerp :default 0)
   (arg-modes fgl-rule-arg-mode-list-p)
   (enabledp booleanp :default t))
  :layout :list)

(fty::deflist fgl-ruledata-list :elt-type fgl-ruledata :true-listp t)

;; Registration metadata is separate from the rune, which identifies a rule.
;; Copy modes and enabled status into executable rules when reading a database.
(fty::deftagsum fgl-rule
  (:rewrite ((rune fgl-rune-p)
             (rule cmr::rewrite-p)
             (arg-modes fgl-rule-arg-mode-list-p)
             (enabledp booleanp :default t))
   :extra-binder-names (hyps lhs rhs equiv)
   :layout :fulltree)
  (:primitive ((name pseudo-fnsym-p)
               (arg-modes fgl-rule-arg-mode-list-p)
               (enabledp booleanp :default t)) :layout :list)
  (:meta ((name pseudo-fnsym-p)
          (arg-modes fgl-rule-arg-mode-list-p)
          (enabledp booleanp :default t)) :layout :list))

(fty::deflist fgl-rulelist :elt-type fgl-rule :true-listp t)

(define fgl-rule->rune ((x fgl-rule-p))
  :returns (rune fgl-rune-p)
  (fgl-rule-case x
    :rewrite x.rune
    :primitive (fgl-rune-primitive x.name)
    :meta (fgl-rune-meta x.name)))

(define fgl-rule->arg-modes ((x fgl-rule-p))
  :returns (modes fgl-rule-arg-mode-list-p)
  (fgl-rule-case x
    :rewrite x.arg-modes
    :primitive x.arg-modes
    :meta x.arg-modes))

(define fgl-rule->enabledp ((x fgl-rule-p))
  :returns (enabledp booleanp)
  (fgl-rule-case x
    :rewrite x.enabledp
    :primitive x.enabledp
    :meta x.enabledp))

(define fgl-rule-rewrite->hyps ((x fgl-rule-p))
  :guard (fgl-rule-case x :rewrite)
  :enabled t
  (cmr::rewrite->hyps (fgl-rule-rewrite->rule x)))

(define fgl-rule-rewrite->lhs ((x fgl-rule-p))
  :guard (fgl-rule-case x :rewrite)
  :enabled t
  (cmr::rewrite->lhs (fgl-rule-rewrite->rule x)))

(define fgl-rule-rewrite->rhs ((x fgl-rule-p))
  :guard (fgl-rule-case x :rewrite)
  :enabled t
  (cmr::rewrite->rhs (fgl-rule-rewrite->rule x)))

(define fgl-rule-rewrite->equiv ((x fgl-rule-p))
  :guard (fgl-rule-case x :rewrite)
  :enabled t
  (cmr::rewrite->equiv (fgl-rule-rewrite->rule x)))




(define fgl-rune->name ((rune fgl-rune-p))
  (fgl-rune-case rune
    :rewrite rune.name
    :definition rune.name
    :formula rune.name
    :primitive rune.name
    :meta rune.name))
