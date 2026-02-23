; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "centaur/meta/congruence" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)


(local (std::add-default-post-define-hook :fix))

(defprod fgl-congruence-rune
  ((name pseudo-fnsym-p))
  :tag :congruence
  :layout :list)

(fty::deflist fgl-congruence-runelist :elt-type fgl-congruence-rune :true-listp t)

(local (in-theory (disable w)))

(fty::deflist congruence-rulelist :elt-type cmr::congruence-rule :true-listp t)

(defprod fgl-id-congruence-rune
  ((name pseudo-fnsym-p))
  :tag :id-congruence
  :layout :list)

(fty::deflist fgl-id-congruence-runelist :elt-type fgl-id-congruence-rune :true-listp t)

(local (in-theory (disable w)))




;; (define fgl-ev-congruence-rulelist-correct-p ((x congruence-rulelist-p))
;;   (if (atom x)
;;       t
;;     (and (fgl-ev-congruence-rule-correct-p (car x))
;;          (fgl-ev-congruence-rulelist-correct-p (cdr x))))
;;   ///
;;   (defthm fgl-ev-congruence-rulelist-correct-p-of-cons
;;     (equal (fgl-ev-congruence-rulelist-correct-p (cons a b))
;;            (and (fgl-ev-congruence-rule-correct-p a)
;;                 (fgl-ev-congruence-rulelist-correct-p b))

(define congruence-rule-from-rune ((rune fgl-congruence-rune-p)
                                   (w plist-worldp))
  :returns (mv errmsg (rule (implies (not errmsg) (cmr::congruence-rule-p rule))))
  (b* ((name (fgl-congruence-rune->name rune))
       (formula (acl2::meta-extract-formula-w name w))
       ((unless (pseudo-termp formula))
        (mv (msg "Bad formula: ~x0" name) nil)))
    (cmr::parse-congruence-rule formula w)))

(define congruence-rules-from-runes ((runes fgl-congruence-runelist-p)
                                     (w plist-worldp))
  :returns (mv errmsg (rules congruence-rulelist-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg1 rule) (congruence-rule-from-rune (car runes) w))
       ((mv errmsg2 rules) (congruence-rules-from-runes (cdr runes) w)))
    (if errmsg1
        (mv errmsg1 rules)
      (mv errmsg2 (cons rule rules)))))











(fty::defmap congruence-rule-table :key-type pseudo-fnsym :val-type congruence-rulelist
  :true-listp t)

(fty::defmap id-congruence-rule-table :key-type pseudo-fnsym :true-listp t)


(define parse-id-congruence-rule ((x pseudo-termp))
  :returns (fnname pseudo-fnsym-p)
  (pseudo-term-case x
    :fncall (and (eq x.fn 'equal)
                 (eql (len x.args) 2)
                 (pseudo-term-case (second x.args) :var)
                 (let ((arg1 (first x.args)))
                   (pseudo-term-case arg1
                     :fncall (and (eql (len arg1.args) 1)
                                  (equal (first arg1.args) (second x.args))
                                  arg1.fn)
                     :otherwise nil)))
    :otherwise nil))

(define check-id-congruence-rune ((rune fgl-id-congruence-rune-p)
                                  (w plist-worldp))
  :returns (mv errmsg (fnname pseudo-fnsym-p))
  (b* ((rune (fgl-id-congruence-rune-fix rune))
       (name (fgl-id-congruence-rune->name rune))
       (formula (acl2::meta-extract-formula-w name w))
       ((unless (pseudo-termp formula))
        (mv (msg "Formula not pseudo-termp: ~x0" rune) nil))
       (fn (parse-id-congruence-rule formula))
       ((unless fn) (mv (msg "Incorrect form for an identity congruence rule: ~x0" rune) nil)))
    (mv nil fn)))

(define id-congruence-table-from-runes ((runes fgl-id-congruence-runelist-p)
                                        (w plist-worldp))
  :returns (mv errmsg (table id-congruence-rule-table-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg fnname) (check-id-congruence-rune (car runes) w))
       ((when errmsg) (mv errmsg nil))
       ((mv errmsg rest) (id-congruence-table-from-runes (cdr runes) w))
       ((when errmsg) (mv errmsg nil)))
    (mv nil (hons-acons fnname t rest))))
       






(define fgl-congruence-runes ((w plist-worldp))
  (cdr (hons-assoc-equal 'fgl-congruence-rules (table-alist 'fgl-congruence-rules w))))

(defmacro add-fgl-congruence (name)
  (let ((rune (fgl-congruence-rune name)))
    `(progn (local (make-event
                    (b* ((rune ',rune)
                         ((mv errmsg &) (congruence-rule-from-rune rune (w state)))
                         ((when errmsg) (er soft 'add-fgl-congruence
                                            "Couldn't extract a congruence rule from ~x0: ~@1"
                                            rune errmsg)))
                      (value '(value-triple :congruence-rule-ok)))))
            (table fgl-congruence-rules 'fgl-congruence-rules
                   (cons ',rune (fgl-congruence-runes world))))))

(define fgl-id-congruence-runes ((w plist-worldp))
  (cdr (hons-assoc-equal 'fgl-id-congruence-rules (table-alist 'fgl-id-congruence-rules w))))

(defmacro add-fgl-id-congruence (name)
  (let ((rune (fgl-id-congruence-rune name)))
    `(progn (local (make-event
                    (b* ((rune ',rune)
                         ((mv errmsg &) (check-id-congruence-rune rune (w state)))
                         ((when errmsg) (er soft 'add-fgl-id-congruence
                                            "Couldn't extract a id-congruence rule from ~x0: ~@1"
                                            rune errmsg)))
                      (value '(value-triple :id-congruence-rule-ok)))))
            (table fgl-id-congruence-rules 'fgl-id-congruence-rules
                   (cons ',rune (fgl-id-congruence-runes world))))))

(local (defun foo (x) x))
(local (add-fgl-id-congruence foo))


(defxdoc add-fgl-congruence
  :parents (fgl-rewrite-rules)
  :short "Add a congruence rule to FGL's theory"
  :long "<p>See @(see acl2::congruence) for a general discussion of congruence rules.</p>

<p>FGL accepts congruence rules similar to those recognized by ACL2, but only
the \"classic\" variety, not \"patterned\" congruences. This macro takes the
name of a congruence rule and adds it to the list of such rules that will be
consumed by FGL.</p>

<p>See also @(see add-fgl-id-congruence) for an additional kind of rule
appropriate to identity functions.</p>")

(defxdoc add-fgl-id-congruence
  :parents (fgl-rewrite-rules)
  :short "Add an identity congruence rule to FGL's theory"
  :long "<p>It is sometimes convenient to use identity functions to mark terms in the
FGL rewriter. A special property of these is that if we are rewriting the call
of an identity function in some equivalence context, it is sound to rewrite the
argument of the identity function in the same equivalence context. This
behavior can't be replicated with regular congruence rules except by proving
such a rule for every equivalence context.</p>

<p>This macro takes a single argument which is the name of a formula of the
form @('(equal (<fn> <var>) <var>)'). Notably, for a function defined using
@('(defun fn (x) x)'), the function's name itself has such a formula. Calling
this macro with such an argument lets FGL use the equivalence context of the
call of fn when rewriting the argument of fn.</p> ")
