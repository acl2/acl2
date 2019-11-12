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
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable pseudo-termp
                           pseudo-term-listp
                           acl2::pseudo-termp-opener)))



(fty::deftagsum fgl-rune
  (:rewrite (name))
  (:definition (name))
  (:formula ((name pseudo-fnsym-p)))
  (:primitive ((name pseudo-fnsym-p)))
  (:meta    ((name pseudo-fnsym-p)))
  :layout :list)

(fty::deflist fgl-runelist :elt-type fgl-rune :true-listp t)


(fty::deftagsum fgl-rule
  (:rewrite ((rune fgl-rune-p)
             (rule cmr::rewrite-p))
   :extra-binder-names (hyps lhs rhs equiv)
   :layout :fulltree)
  (:primitive ((name pseudo-fnsym-p)) :layout :list)
  (:meta      ((name pseudo-fnsym-p)) :layout :list))

(fty::deflist fgl-rulelist :elt-type fgl-rule :true-listp t)

(define fgl-rule->rune ((x fgl-rule-p))
  :returns (rune fgl-rune-p
                 :hints((and stable-under-simplificationp
                             '(:in-theory (enable fgl-rule-fix fgl-rune-p)))))
  (fgl-rule-case x
    :rewrite x.rune
    :otherwise (fgl-rule-fix x)))

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




(fty::deftagsum fgl-binder-rune
  (:brewrite (name))
  (:bformula ((name pseudo-fnsym-p)))
  (:bmeta ((name pseudo-fnsym-p)))
  :layout :list)

(fty::deflist fgl-binder-runelist :elt-type fgl-binder-rune :true-listp t)

(fty::deftagsum fgl-binder-rule
  (:brewrite ((rune fgl-binder-rune-p)
              (lhs-fn pseudo-fnsym-p)
              (lhs-args pseudo-term-listp)
              (hyps pseudo-term-listp)
              (rhs pseudo-termp)
              (equiv pseudo-fnsym-p)
              (r-equiv pseudo-fnsym-p))
   :layout :fulltree)
  (:bmeta      ((name pseudo-fnsym-p)) :layout :list))

(fty::deflist fgl-binder-rulelist :elt-type fgl-binder-rule :true-listp t)

(define fgl-binder-rule->rune ((x fgl-binder-rule-p))
  :returns (rune fgl-binder-rune-p
                 :hints((and stable-under-simplificationp
                             '(:in-theory (enable fgl-binder-rule-fix fgl-binder-rune-p)))))
  (fgl-binder-rule-case x
    :brewrite x.rune
    :bmeta (fgl-binder-rule-fix x)))

(fty::deftranssum fgl-generic-rune
  (fgl-binder-rune
   fgl-rune))

(fty::deftranssum fgl-generic-rule
  (fgl-binder-rule
   fgl-rule))

(defthmd tag-when-fgl-generic-rule-p
  (implies (fgl-generic-rule-p x)
           (and (implies (member (tag x) '(:brewrite :bmeta))
                         (equal (fgl-binder-rule-kind x) (tag x)))
                (implies (not (member (tag x) '(:brewrite :bmeta)))
                         (equal (fgl-rule-kind x) (tag x)))))
  :hints(("Goal" :in-theory (enable fgl-binder-rule-kind
                                    fgl-rule-kind
                                    fgl-generic-rule-p
                                    fgl-rule-p
                                    fgl-binder-rule-p
                                    tag))))

(defthmd fgl-generic-rune-p-when-fgl-generic-rule-p
  (implies (and (fgl-generic-rule-p x)
                (not (member (tag x) '(:brewrite :rewrite))))
           (fgl-generic-rune-p x))
  :hints(("Goal" :in-theory (enable fgl-generic-rule-p
                                    fgl-generic-rune-p
                                    fgl-rule-p
                                    fgl-rune-p
                                    fgl-binder-rule-p
                                    fgl-binder-rune-p
                                    tag))))

(define fgl-generic-rule->rune ((x fgl-generic-rule-p))
  :returns (rune fgl-generic-rune-p)
  :prepwork ((local (in-theory (enable tag-when-fgl-generic-rule-p
                                       fgl-generic-rune-p-when-fgl-generic-rule-p))))
  ;; :guard-hints (("goal" :in-theory (enable fgl-generic-rule-fix fgl-generic-rule-p)))
  (b* ((x (fgl-generic-rule-fix x)))
    (case (tag x)
      (:rewrite (fgl-rule-rewrite->rune x))
      (:brewrite (fgl-binder-rule-brewrite->rune x))
      (otherwise x))))
