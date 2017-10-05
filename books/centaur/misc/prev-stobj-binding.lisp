; Originally from AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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


(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

;; In the aignet library we used the following reasoning strategy: most
;; functions that updated an aignet structure would return an _extension_ of
;; the input aignet.  The fact that the output was an extension of the input
;; implied a whole array of properties.  Instead of proving the properties of
;; every such function, we'd just prove that it produced an extension, and
;; prove the properties of any extension.  However, we ran into the following
;; kind of problem often:

;; (implies (and (aignet-extension-p new old)
;;               (<= (nfix n) (num-nodes old)))
;;          (equal (lookup-id n new) (lookup-id n old)))

;; This rule isn't very good because old is a free variable, and it just looks
;; for matches by looking for (aignet-extension-p new old) in the type-alist,
;; which doesn't often work.  But crucially, in most cases new is a return
;; value of some function, and we want old to be one of the inputs to that
;; function.  Since aignets are stobjs, we can exploit functions' stobjs-in and
;; stobjs-out properties to determine which input to bind old to. The following
;; functions implement this strategy.

;; This can be extended to work with non-stobjs or non-executable functions by
;; maintaining a table, prev-stobjs-table, containing fake stobjs-out and
;; formals for various functions.  These set up the correspondence between
;; outputs and inputs of the functions bound there.

(defun prev-stobjs-correspondence (fn w)
  (b* ((table (table-alist 'prev-stobjs-table w))
       (look (cdr (assoc-eq fn table)))
       ((when look)
        (mv (car look) (cadr look))))
    (mv (acl2::stobjs-out fn w)
        (acl2::formals fn w))))

(defmacro set-prev-stobjs-correspondence (fn &key stobjs-out formals)
  `(table prev-stobjs-table ',fn '(,stobjs-out ,formals)))

(set-prev-stobjs-correspondence update-nth :stobjs-out (stobj) :formals (n val stobj))
(set-prev-stobjs-correspondence update-nth-array :stobjs-out (stobj) :formals (j k val stobj))
(set-prev-stobjs-correspondence cons :stobjs-out (stobj) :formals (x stobj))


(defun find-prev-stobj-binding (new-term state)
  (declare (xargs :guard (pseudo-termp new-term)
                  :stobjs state
                  :mode :program))
  (b* (((mv valnum function args)
        ;; valnum is the output number of function corresponding to new-term.
        ;; If new-term is of a bad form, bind valnum = nil and we'll abort.
        (case-match new-term
          (('mv-nth ('quote valnum) (function . args) . &)
           (mv (and (symbolp function) valnum) function args))
          ((function . args)
           (mv (and (symbolp function) 0) function args))
          (& (mv nil nil nil))))
       ((unless valnum) (mv nil nil))
       ((when (or (eq function 'if)
                  (eq function 'return-last)))
        ;; Can't call stobjs-out on either of these
        (mv nil nil))
       (w (w state))
       ((mv stobjs-out formals) (prev-stobjs-correspondence function w))
       (stobj-out (nth valnum stobjs-out))
       ((unless stobj-out) (mv nil nil))
       (pos (position stobj-out formals))
       ((unless pos) (mv nil nil)))
    (mv t (nth pos args))))


(defun prev-stobj-binding (new-term prev-var mfc state)
  (declare (xargs :guard (and (pseudo-termp new-term)
                              (symbolp prev-var))
                  :stobjs state
                  :mode :program)
           (ignore mfc))
  (b* (((mv ok prev-term) (find-prev-stobj-binding new-term state)))
    (if (and ok (not (equal new-term prev-term)))
        (if prev-term
            `((,prev-var . ,prev-term))
          (er hard? 'prev-stobj-binding
              "prev-term was nil, new-term: ~x0~%Bad entry in prev-stobjs-table?~%" new-term))
      ;; This binding is here so that in certain cases the rule can still apply
      ;; by falling through the bind-free and binding prev-var elsewhwere.
      `((do-not-use-this-long-horrible-variable
         . do-not-use-this-long-horrible-variable)))))

;; Usage, from the example above:
;; (implies (and (bind-free (prev-stobj-binding new 'old mfc state))
;;               (aignet-extension-p new old)
;;               (<= (nfix n) (num-nodes old)))
;;          (equal (lookup-id n new) (lookup-id n old)))

