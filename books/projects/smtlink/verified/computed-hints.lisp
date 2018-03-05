;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a computed hint that looks for the function
;; "SMT-please"

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)


(defsection SMT-computed-hints
  :parents (verified)
  :short "Define Smtlink computed-hints"

  (defconst *SMT-computed-hints-table*
    '((process-hint . SMT-verified-cp-hint)
      (smt-hint . nil)
      (main-hint . nil)
      (A-hint . nil)))

  (program)

  (define extract-hint-wrapper (cl)
    (cond ((endp cl) (mv nil nil nil))
          (t (b* ((lit cl))
               (case-match lit
                 ((('hint-please ('quote kwd-alist) ('quote tag)) . term)
                  (mv term kwd-alist tag))
                 (& (extract-hint-wrapper (cdr cl))))))))

  (define ch-replace (next-stage)
    (if (equal next-stage nil)
        nil
      `((,next-stage clause))))

  (define treat-in-theory-hint (kwd-alist)
    (mv-let (pre post)
      (split-keyword-alist :in-theory kwd-alist)
      (cond ((and post
                  (equal (caadr post) 'enable))
             `(,@pre
               :in-theory (enable hint-please ,@(cdadr post))
               ,@(cddr post)))
            ((and post
                  (equal (caadr post) 'disable))
             `(,@pre
               :in-theory (e/d (hint-please) (,@(cdadr post)))
               ,@(cddr post)))
            ((and post
                  (equal (caadr post) 'e/d))
             `(,@pre
               :in-theory (e/d (hint-please ,@(car (cdadr post))) (,@(cadr (cdadr post))))
               ,@(cddr post)))
            (t `(;; :do-not '(preprocess)
                 :in-theory (enable hint-please)
                 ,@kwd-alist
                 )))))

  (define SMT-verified-cp-hint (cl)
    (b* (((mv & kwd-alist tag) (extract-hint-wrapper cl))
         (next-stage (cdr (assoc tag *SMT-computed-hints-table*)))
         (ch-replace-hint (ch-replace next-stage))
         (rest-hint (treat-in-theory-hint kwd-alist)))
      `(:computed-hint-replacement
        ,ch-replace-hint
        ,@rest-hint)))

  (define SMT-process-hint (cl)
    (b* (((mv & kwd-alist tag) (extract-hint-wrapper cl))
         (next-stage (cdr (assoc tag *SMT-computed-hints-table*))))
      `(:computed-hint-replacement
        ,(ch-replace next-stage)
        ;; :do-not '(preprocess)
        ,@kwd-alist)))

  (logic)

  )
;; Add this line to your code to add a default hint of Smtlink
;; (add-default-hints '((SMT-computed-hint clause)))
;; Remove hint:
;; (remove-default-hints '((SMT-computed-hint clause)))
