; Centaur Meta-reasoning Library
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

(in-package "CMR")

(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)



(local (acl2::def-ev-pseudo-term-fty-support acl2::mextract-ev acl2::mextract-ev-lst))

(defines term-variable-free-p
  (define term-variable-free-p ((x pseudo-termp))
    :measure (pseudo-term-count x)
    :returns var-free-p
    (pseudo-term-case x
      :const t
      :var nil
      :call (termlist-variable-free-p x.args)))
  (define termlist-variable-free-p ((x pseudo-term-listp))
    :measure (pseudo-term-list-count x)
    :returns var-free-p
    (if (atom x)
        t
      (and (termlist-variable-free-p (cdr x))
           (term-variable-free-p (car x)))))
  ///

  (local (defthm member-of-nil
           (equal (member k nil) nil)
           :hints(("Goal" :in-theory (enable member)))))
  (defret-mutual norm-alist-when-variable-free
    (defret norm-alist-when-<fn>
      (implies (and (syntaxp (not (equal a ''nil)))
                    var-free-p)
               (equal (acl2::mextract-ev x a)
                      (acl2::mextract-ev x nil)))
      :hints((and stable-under-simplificationp
                  '(:in-theory (enable acl2::mextract-ev-when-pseudo-term-call))))
      :fn term-variable-free-p)
    (defret norm-alist-when-<fn>
      (implies (and (syntaxp (not (equal a ''nil)))
                    var-free-p)
               (equal (acl2::mextract-ev-lst x a)
                      (acl2::mextract-ev-lst x nil)))
      :fn termlist-variable-free-p))

  (fty::deffixequiv-mutual term-variable-free-p))

(define execute-term-when-variable-free ((x pseudo-termp) mfc state)
  (declare (ignore mfc))
  :prepwork ((local (in-theory (disable w pseudo-termp acl2::magic-ev logic-fnsp))))
  :returns (new-x pseudo-termp)
  (b* ((x (acl2::pseudo-term-fix x)))
    (if (and (cmr::term-variable-free-p x)
             (acl2::logic-fnsp x (w state)))
        (b* (((mv err val) (acl2::magic-ev x nil state t nil)))
          (if err
              x
            (acl2::pseudo-term-quote val)))
      x))
  ///
  (defthm execute-term-when-variable-free-correct
    (implies (acl2::mextract-ev-global-facts)
             (equal (acl2::mextract-ev (execute-term-when-variable-free x mfc state)
                                       a)
                    (acl2::mextract-ev x a)))))


(defun def-force-execute-fn (thmname fn-or-fns equiv)
  (declare (xargs :guard (and (symbolp thmname)
                              (symbolp equiv)
                              (or (symbolp fn-or-fns)
                                  (symbol-listp fn-or-fns)))
                  :mode :program))
  `(defthm ,thmname
    (implies (and (pseudo-termp x)
                  (alistp a)
                  (acl2::mextract-ev-global-facts))
             (,(or equiv 'equal) (acl2::mextract-ev x a)
                    (acl2::mextract-ev (execute-term-when-variable-free x mfc state)
                                       a)))
    :hints(("Goal" :in-theory '(execute-term-when-variable-free-correct)))
    :rule-classes ((:meta :trigger-fns ,(if (atom fn-or-fns)
                                            `(,fn-or-fns)
                                          fn-or-fns)))))

(defmacro def-force-execute (thmname fn-or-fns &key equiv)
  (def-force-execute-fn thmname fn-or-fns equiv))
