; Use Rp-rewriter, then FGL as clause-processors (and some other things in between)
;
; Copyright (C) 2021 Centaur Technology
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "RP")

(include-book "top")
(include-book "centaur/fgl/portcullis" :dir :system)
(include-book "centaur/meta/let-abs" :dir :system)


;; (local
;;  (include-book "centaur/gl/bfr-satlink" :dir :system))

;; (local
;;  (value-triple (acl2::tshell-ensure)))



(defevaluator letabs-ev2 letabs-ev2-list
  ((if a b c)
   (implies a b)
   (not a))
  :namedp t)

(defthm letabs-ev2-of-let-abstract-term
  (equal (letabs-ev2 (cmr::let-abstract-term cmr::x cmr::base-var) acl2::a)
         (letabs-ev2 cmr::x acl2::a))
  :hints (("goal" :use ((:functional-instance cmr::letabs-ev-of-let-abstract-term
                                              (cmr::letabs-ev letabs-ev2)
                                              (cmr::letabs-ev-list letabs-ev2-list )))
           :in-theory (enable letabs-ev2-of-fncall-args
                              letabs-ev2-of-bad-fncall
                              letabs-ev2-of-nonsymbol-atom))))

(define cmr::let-abstract-full-clause-proc-exclude-hyps
  ((clause pseudo-term-listp)
   var)
  (b* (((unless (acl2::pseudo-var-p var)) (list clause))
       (term (acl2::disjoin clause)))
    (case-match term
      (('implies p q)
       (let* ((p (cmr::let-abstract-term p var))
              (q (cmr::let-abstract-term q var)))
         (list (list `(implies ,p ,q)))))
      (&
       (list (list (cmr::let-abstract-term term var))))))
  ///
  
  (defthm cmr::let-abstract-full-clause-proc-exclude-hyps-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (letabs-ev2
                   (acl2::conjoin-clauses
                    (cmr::let-abstract-full-clause-proc-exclude-hyps clause
                                                                     var))
                   a))
             (letabs-ev2 (acl2::disjoin clause) a))
    :rule-classes :clause-processor
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (ACL2::DISJOIN) ()))))) 


(defmacro defthmrp-then-fgl (name term
                                  &key
                                  (rule-classes ':rewrite)
                                  ;; (use-opener-error-rules 't)
                                  (new-synps 'nil)
                                  (disable-meta-rules 'nil)
                                  (enable-meta-rules 'nil)
                                  (enable-rules 'nil)
                                  (disable-rules 'nil)
                                  (runes 'nil)
                                  (runes-outside-in 'nil) ;; when nil, runes will be read from
                                  ;; rp-rules table
                                  (not-simplified-action ':none)
                                  )
  `(encapsulate
     nil
     (make-event
      (b* ((- (check-if-clause-processor-up-to-date (w state)))
           ;;(?old-not-simplified-action (not-simplified-action rp-state))
           (rp-state (update-not-simplified-action ,not-simplified-action rp-state))
           (body `(with-output
                    :stack :pop
                    :on (acl2::summary acl2::event acl2::error)
                    :gag-mode :goals
                    :summary-off (:other-than acl2::time acl2::rules)
                    (def-rp-rule ,',name ,',term
                      :rule-classes ,',rule-classes
                      :hints
                      ('(:clause-processor
                         (rp-cl :runes ,,runes
                                :runes-outside-in ,,runes-outside-in
                                :new-synps ,',new-synps))
                       '(:clause-processor (cmr::let-abstract-full-clause-proc-exclude-hyps
                                            clause 'var))
                       '(:clause-processor fgl::expand-an-implies-cp)
                       '(:clause-processor (fgl::fgl-interp-cp clause (fgl::default-fgl-config)
                                                               fgl::interp-st
                                                               state))
                       )

                      )))
           (event 
            ,(if (or disable-meta-rules
                     enable-meta-rules
                     enable-rules
                     disable-rules)
                 ``(with-output
                     :off :all
                     :stack :push
                     (encapsulate
                       nil

                       ,@(if ',enable-meta-rules
                             `((local
                                (enable-meta-rules ,@',enable-meta-rules)))
                           'nil)

                       ,@(if ',disable-meta-rules
                             `((local
                                (disable-meta-rules ,@',disable-meta-rules)))
                           'nil)

                       ,@(if ',enable-rules
                             `((local
                                (enable-rules ,',enable-rules)))
                           'nil)

                       ,@(if ',disable-rules
                             `((local
                                (disable-rules ,',disable-rules)))
                           'nil)
                       ,body))
               `body)))
        (mv nil event state rp-state)))

     (make-event
      (b* ((rp-state (update-not-simplified-action :error rp-state)))
        (mv nil `(value-triple :none) state rp-state)))
     
     ))
