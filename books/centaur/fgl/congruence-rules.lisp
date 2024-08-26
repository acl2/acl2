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
