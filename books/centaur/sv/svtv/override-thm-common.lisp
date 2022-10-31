; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "override-common")



(std::def-primitive-aggregate svtv-generalized-thm
  (name
   override-vars
   input-vars
   input-var-bindings
   output-vars
   output-parts
   output-part-vars
   hyp
   concl
   svtv
   ideal
   enable
   triples-name
   triple-val-alist
   lemma-nonlocal
   lemma-defthm
   lemma-args
   no-lemmas
   no-integerp
   final-defthm
   final-args
   hints
   constlist-hyp
   rule-classes
   pkg-sym))

(program)


(defun svtv-genthm-input-var-bindings-alist-termlist (input-var-bindings)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(cons ',name ,term)
          (svtv-genthm-input-var-bindings-alist-termlist (cdr input-var-bindings)))))

(defun svtv-genthm-var-alist-termlist (vars)
  (if (atom vars)
      nil
    (b* ((name (car vars)))
      (cons `(cons ',name ,name)
            (svtv-genthm-var-alist-termlist (cdr vars))))))

(defun svtv-genthm-override-test-alist (override-valnames triple-val-alist triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (valvar (car override-valnames))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svtv-override-triple trip))
       ((unless (svex-case trip.test :var))
        (svtv-genthm-override-test-alist (cdr override-valnames) triple-val-alist triples-name)))
    (cons (cons (svex-var->name trip.test) -1)
          (svtv-genthm-override-test-alist (cdr override-valnames) triple-val-alist triples-name))))

(defun svtv-genthm-integerp-conclusions-aux (outputs)
  (if (Atom outputs)
      nil
    (cons `(integerp ,(car outputs))
          (svtv-genthm-integerp-conclusions-aux (cdr outputs)))))

(defun svtv-genthm-output-expressions (x)
  (b* (((svtv-generalized-thm x)))
    (append (set-difference-eq x.output-vars x.output-part-vars)
            x.output-parts)))

(defun svtv-genthm-integerp-conclusions (x)
  (svtv-genthm-integerp-conclusions-aux
   (svtv-genthm-output-expressions x)))

(defun svtv-genthm-initial-override-lemma (x)
  (declare (Xargs :mode :program))
  (b* (((svtv-generalized-thm x))
       (template '(<defthm> <name>-override-lemma
                    (implies <hyp>
                             (b* ((run (svtv-run (<svtv>)
                                                 (append <input-bindings>
                                                         <input-vars>
                                                         <override-tests>
                                                         <override-vals>)
                                                 :include '<outputs-list>))
                                  ((svassocs <outputs>) run))
                               (and <integerp-concls>
                                    <concl>)))
                    <args>)))
    (acl2::template-subst
     template
     :atom-alist `((<defthm> . ,x.lemma-defthm)
                   (<hyp> . ,x.hyp)
                   (<svtv> . ,x.svtv)
                   (<concl> . ,x.concl)
                   (<input-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings)))
                   (<input-vars> . (list . ,(svtv-genthm-var-alist-termlist x.input-vars)))
                   (<override-tests> . ',(svtv-genthm-override-test-alist x.override-vars x.triple-val-alist x.triples-name))
                   (<override-vals> . (list . ,(svtv-genthm-var-alist-termlist x.override-vars)))
                   (<outputs-list> . ,x.output-vars))
     :splice-alist `((<outputs> . ,x.output-vars)
                     (<integerp-concls> . ,(if x.no-integerp nil (svtv-genthm-integerp-conclusions x)))
                     (<args> . ,x.lemma-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :pkg-sym x.pkg-sym)))



(defun svtv-genthm-override-svassocs (override-valnames triple-val-alist triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (valvar (car override-valnames))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svtv-override-triple trip)))
    (cons (if (eq valvar trip.refvar)
              valvar
            `(,valvar ',trip.refvar))
          (svtv-genthm-override-svassocs (cdr override-valnames) triple-val-alist triples-name))))


(defun svtv-genthm-input-binding-hyp-termlist (input-var-bindings)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(equal ,name ,term)
          (svtv-genthm-input-binding-hyp-termlist (cdr input-var-bindings)))))




(defun svtv-genthm-input-var-instantiation (input-vars)
  (if (atom input-vars)
      nil
    (cons `(,(car input-vars) (svex-env-lookup ',(car input-vars) env))
          (svtv-genthm-input-var-instantiation (cdr input-vars)))))




(defun find-illegal-variable (x)
  (if (atom x)
      nil
    (if (acl2::legal-variablep (car x))
        (find-illegal-variable (cdr x))
      x)))
    

(defun svtv-genthm-check-variable-list (name x)
  (b* ((illegal-tail (find-illegal-variable x))
       ((when illegal-tail)
        (msg "~s0 must be a list of legal variables, but contains ~x1" name (car illegal-tail)))
       (dup-tail (acl2::hons-dups-p x))
       ((when dup-tail)
        (msg "~s0 cannot contain duplicates but ~x1 is duplicated" name (car dup-tail))))
    nil))

(defun svtv-genthm-error (x)
  (b* (((svtv-generalized-thm x)))
    (or (svtv-genthm-check-variable-list "Override-vars" x.override-vars)
        (svtv-genthm-check-variable-list "Input-vars" x.input-vars)
        (svtv-genthm-check-variable-list "Output-vars" x.output-vars)
        (and (not (acl2::doublet-listp x.input-var-bindings))
             "Input-var-bindings must be a list of two-element lists")
        (svtv-genthm-check-variable-list "Keys of input-var-bindings" (strip-cars x.input-var-bindings))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars
                                                   (strip-cars x.input-var-bindings)
                                                   x.override-vars
                                                   x.output-vars))))
          (and dup-tail
               (msg "Input, output, and override variables should not ~
                     intersect, but ~x0 is present in more than one"
                    (car dup-tail)))))))




(defun svtv-genthm-translate-lst (x ctx w state)
  (declare (xargs :stobjs state))
  (if (atom x)
      (value nil)
    (er-let* ((first (acl2::translate (car x) t nil nil ctx w state))
              (rest (svtv-genthm-translate-lst (cdr x) ctx w state)))
      (value (cons first rest)))))

(define svtv-unsigned-byte-hyps ((x svar-boolmasks-p))
  :hooks nil
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x)))) (svtv-unsigned-byte-hyps (cdr x)))
       ((cons var mask) (car x)))
    (cons `(unsigned-byte-p ,(integer-length mask) ,var)
          (svtv-unsigned-byte-hyps (cdr x)))))
