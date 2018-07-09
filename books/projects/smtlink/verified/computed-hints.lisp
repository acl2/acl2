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

(include-book "hint-interface")

(defsection SMT-computed-hints
  :parents (verified)
  :short "Define Smtlink computed-hints"

  ;; verified version of split-kwd-alist
  (define my-split-kwd-alist ((key symbolp)
                              (kwd-alist true-listp))
    :returns (mv (pre true-listp)
                 (post true-listp))
    :measure (len kwd-alist)
    :hints (("Goal" :in-theory (disable true-list-fix-preserve-length)
             :use ((:instance true-list-fix-preserve-length
                              (x kwd-alist)))))
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((unless (consp kwd-alist)) (mv nil nil))
         ((if (eq key (car kwd-alist)))
          (mv nil kwd-alist))
         ((unless (consp (cdr kwd-alist)))
          (prog2$ (er hard? 'SMT-computed-hints=>my-split-kwd-alist "Something ~
  is wrong with the kwd-alist: ~q0" kwd-alist)
                  (mv nil nil)))
         ((mv pre post)
          (my-split-kwd-alist key (cddr kwd-alist))))
      (mv (cons (car kwd-alist)
                (cons (cadr kwd-alist)
                      pre))
          post)))

  (define treat-in-theory-hint ((enabled true-listp)
                                (kwd-alist true-listp))
    :returns (new-kwd-alist
              true-listp
              :hints (("Goal"
                       :in-theory (disable
                                   true-listp-of-my-split-kwd-alist.post)
                       :use ((:instance
                              true-listp-of-my-split-kwd-alist.post
                              (key :in-theory)
                              (kwd-alist (true-list-fix kwd-alist)))))))
    :guard-debug t
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((mv pre post)
          (my-split-kwd-alist :in-theory kwd-alist)))
      (cond ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (equal (caadr post) 'enable))
             `(,@pre
               :in-theory (enable ,@enabled ,@(cdadr post))
               ,@(cddr post)))
            ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (equal (caadr post) 'disable))
             `(,@pre
               :in-theory (e/d ,enabled (,@(cdadr post)))
               ,@(cddr post)))
            ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (consp (cdadr post))
                  (consp (cddadr post))
                  (equal (caadr post) 'e/d))
             `(,@pre
               :in-theory (e/d (,@enabled ,@(car (cdadr post)))
                               (,@(cadr (cdadr post))))
               ,@(cddr post)))
            (t `(;; :do-not '(preprocess)
                 :in-theory (enable ,@enabled)
                            ,@kwd-alist
                            )))))

  (define treat-expand-hint ((expand-lst true-listp) (kwd-alist true-listp))
    :returns (new-kwd-alist
              true-listp
              :hints (("Goal"
                       :in-theory (disable
                                   true-listp-of-my-split-kwd-alist.post)
                       :use ((:instance
                              true-listp-of-my-split-kwd-alist.post
                              (key :expand)
                              (kwd-alist (true-list-fix kwd-alist)))))))
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((mv pre post)
          (my-split-kwd-alist :expand kwd-alist)))
      (cond ((and (consp post)
                  (consp (cdr post)))
             `(,@pre
               :expand (,@expand-lst
                        ,@(cadr post))
               ,@post))
            (t ; simply extend kwd-alist
             `(:expand ,@expand-lst
                       ,@kwd-alist)))))

  (program)
  (define extract-hint-wrapper (cl)
    (cond ((endp cl) (mv nil nil))
          (t (b* ((lit cl))
               (case-match lit
                 ((('hint-please ('quote kwd-alist)) . term)
                  (mv term kwd-alist))
                 (& (extract-hint-wrapper (cdr cl))))))))

  (define SMT-process-hint (cl)
    (b* (((mv & kwd-alist) (extract-hint-wrapper cl)))
      `(:computed-hint-replacement
        ((SMT-process-hint clause))
        ,@kwd-alist)))

  (logic)

  )
;; Add this line to your code to add a default hint of Smtlink
;; (add-default-hints '((SMT-computed-hint clause)))
;; Remove hint:
;; (remove-default-hints '((SMT-computed-hint clause)))
