; Tool to auto-generate theorems about functions that build dags
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also wf-dagp.

;; TODO: Add support for mutual-recursion
;; TODO: Maybe split he corollaries into a different tool

(include-book "dag-parent-array")
(include-book "wf-dagp")

(defun index-of-simple (item lst)
  (if (endp lst)
      nil
    (if (equal item (first lst))
        0
      (+ 1 (index-of-simple item (rest lst))))))

;; This is for functions that return an erp as well as the 5 parts of the dag (dag-array, dag-len, dag-parent-array, dag-constant-alist, dag-variable-alist).
(defun def-dag-builder-theorems-fn (call ret-spec dag-array-name dag-parent-array-name hyps hyps-everywhere hints recursivep expand dont-enable)
  (b* ((dag-array-name (if dag-array-name dag-array-name ''dag-array))
       (dag-parent-array-name (if dag-parent-array-name dag-parent-array-name ''dag-parent-array))
       (return-vals (cdr ret-spec))
       (expected-return-vals '(erp dag-len dag-array dag-parent-array dag-variable-alist dag-constant-alist))
       ((when (not (subsetp-eq expected-return-vals ret-spec)))
        (er hard? 'def-dag-builder-theorems-fn "Missing return values: ~x0." (set-difference-eq expected-return-vals ret-spec)))
       (fn (ffn-symb call))
       ;; Figure out the numbers that indicate the parts of the return value:
       (dag-len-rv (index-of-simple 'dag-len return-vals))
       (dag-array-rv (index-of-simple 'dag-array return-vals))
       (dag-parent-array-rv (index-of-simple 'dag-parent-array return-vals))
       (dag-constant-alist-rv (index-of-simple 'dag-constant-alist return-vals))
       (dag-variable-alist-rv (index-of-simple 'dag-variable-alist return-vals))
       (erp-rv (index-of-simple 'erp return-vals)))
    `(progn
       ;; The dag-len returned is a natp.
       ;; note: no wf-dagp hyp, no exclusion of the error case
       (defthm ,(pack$ 'natp-of-mv-nth- dag-len-rv '-of- fn)
         (implies (and ,@(and hyps-everywhere hyps)
                       ;; todo:
                       ;; ,@(and hyps-everywhere `((not (mv-nth ,erp-rv ,call)))) ;no error
                       (natp dag-len))
                  (natp (mv-nth ,dag-len-rv ,call)))
         :rule-classes (:rewrite :type-prescription)
         :hints ,(or hints
                     `(("Goal" ,@(and recursivep `(:induct ,call))
                        ,@(and expand `(:expand ,expand))
                        :in-theory (enable ,@(and (not dont-enable) (list fn))
                                           ,@(and recursivep `((:i ,fn))))))))

       ;; TODO: Some of these only make sense if a DAG is passed in...

       ;; The dag-len doesn't get smaller.
       ;; compare to one below?
       ;; note: no wf-dagp hyp, no exclusion of the error case
       (defthm ,(pack$ 'bound-on-mv-nth- dag-len-rv '-of- fn '- 3) ;todo drop the -3 from the name?
         (implies (and ,@(and hyps-everywhere hyps)
                       ;; todo:
                       ;; ,@(and hyps-everywhere `((not (mv-nth ,erp-rv ,call)))) ;no error
                       (natp dag-len))
                  (<= dag-len
                      (mv-nth ,dag-len-rv ,call)))
         :rule-classes ((:linear :trigger-terms ((mv-nth ,dag-len-rv ,call))))
         :hints ,(or hints
                     `(("Goal" ,@(and recursivep `(:induct ,call))
                        ,@(and expand `(:expand ,expand))
                        :in-theory (enable ,@(and (not dont-enable) (list fn))
                                           ,@(and recursivep `((:i ,fn))))))))

      ;; compare to one below?
       (defthm ,(pack$ 'bound-on-mv-nth- dag-len-rv '-of- fn '- 3 '-gen) ;todo drop the -3 from the name?
         (implies (and ,@(and hyps-everywhere hyps)
                       ;; todo: exclude the error case?
                       (natp dag-len)
                       (<= bound dag-len))
                  (<= bound (mv-nth ,dag-len-rv ,call)))
         :hints ,(or hints
                     `(("Goal" ,@(and recursivep `(:induct ,call))
                        ,@(and expand `(:expand ,expand))
                        :in-theory (enable ,@(and (not dont-enable) (list fn))
                                           ,@(and recursivep `((:i ,fn))))))))

       ;; This main theorem, proves wf-dagp
       (defthm ,(pack$ 'type-of- fn)
         (implies (and (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error (todo: option to drop this since often errors leave everything unchanged?)
                       ,@hyps)
                  (and (wf-dagp ,dag-array-name
                                (mv-nth ,dag-array-rv ,call)
                                (mv-nth ,dag-len-rv ,call)
                                ,dag-parent-array-name
                                (mv-nth ,dag-parent-array-rv ,call)
                                (mv-nth ,dag-constant-alist-rv ,call)
                                (mv-nth ,dag-variable-alist-rv ,call))
                       (<= dag-len (mv-nth ,dag-len-rv ,call)) ; usually provable separately?

                    ))
         :otf-flg t
         :hints  ,(or hints
                      `(("Goal"
                         ,@(and recursivep `(:induct ,call))
                         ,@(and expand `(:expand ,expand))
                         :do-not '(generalize eliminate-destructors)
                         :in-theory (e/d (,@(and (not dont-enable) (list fn))
                                          ,@(and recursivep `((:i ,fn)))
                                          ;wf-dagp ;todo: just use wf-dagp throughout?
                                          )
                                         (bounded-dag-parent-arrayp pseudo-dag-arrayp natp))))))

       ;;implied by wf-dagp
       (defthm ,(pack$ 'type-of- fn '-one)
         (implies (and (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                  (<= (mv-nth ,dag-len-rv ,call)
                      2147483646))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory '(wf-dagp-forward-to-<=-of-len))))

       ;; corollary to generalize
       (defthm ,(pack$ 'type-of- fn '-two)
         (implies (and (<= bound$ dag-len)
                       (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                  (<= bound$ (mv-nth ,dag-len-rv ,call)))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory (disable ,(pack$ 'type-of- fn)))))

       ;; todo: the n$ here should not clash with any vars in the call
       ;; corollary to generalize
       (defthm ,(pack$ 'type-of- fn '-three)
         (implies (and (<= n$ (mv-nth ,dag-len-rv ,call))
                       (natp n$)
                       (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                   (pseudo-dag-arrayp ,dag-array-name
                                      (mv-nth ,dag-array-rv ,call)
                                      n$))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory '(wf-dagp
                               pseudo-dag-arrayp-monotone
                               natp
                               pseudo-dag-arrayp-forward-to-natp-arg3
                               natp-compound-recognizer))))

       ;; implied by wf-dagp (someday, when wf-dagp is never opened, we might not need this)
       (defthm ,(pack$ 'type-of- fn '-four)
         (implies (and (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                   (array1p ,dag-array-name (mv-nth ,dag-array-rv ,call)))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory '(wf-dagp
                               ;natp
                               pseudo-dag-arrayp
                               ;;natp-compound-recognizer
                               ))))

       ;; implied by wf-dagp (someday, when wf-dagp is never opened, we might not need this)
       (defthm ,(pack$ 'bounded-dag-parent-arrayp-of-mv-nth- dag-parent-array-rv '-of- fn)
         (implies (and (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                  (bounded-dag-parent-arrayp ,dag-parent-array-name
                                             (mv-nth ,dag-parent-array-rv ,call)
                                             (mv-nth ,dag-len-rv ,call)))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory '(wf-dagp))))

       ;; implied by wf-dagp (someday, when wf-dagp is never opened, we might not need this)
       (defthm ,(pack$ 'bounded-dag-dag-constant-alistp-of-mv-nth- dag-constant-alist-rv '-of- fn)
         (implies (and (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                  (bounded-dag-constant-alistp (mv-nth ,dag-constant-alist-rv ,call)
                                               (mv-nth ,dag-len-rv ,call)))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory '(wf-dagp-forward))))

       ;; implied by wf-dagp (someday, when wf-dagp is never opened, we might not need this)
       (defthm ,(pack$ 'bounded-dag-dag-variable-alistp-of-mv-nth- dag-variable-alist-rv '-of- fn)
         (implies (and (wf-dagp ,dag-array-name dag-array dag-len ,dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth ,erp-rv ,call)) ;no error
                       ,@hyps)
                  (bounded-dag-variable-alistp (mv-nth ,dag-variable-alist-rv ,call)
                                               (mv-nth ,dag-len-rv ,call)))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of- fn))
                  :in-theory '(wf-dagp-forward))))

       ;; This one takes hyps
       ;; (defthm ,(pack$ 'pseudo-dag-arrayp-of-mv-nth- dag-array-rv '-of- fn)
       ;;   (implies (and (dag-pseudo-dag-arrayp2 ,dag-array-name dag-array dag-len)
       ;;                 (bounded-dag-parent-arrayp ,dag-parent-array-name dag-parent-array dag-len)
       ;;                 (not (mv-nth ,erp-rv ,call))
       ;;                 (<= dag-len 2147483646)
       ;;                 (dag-constant-alistp dag-constant-alist)
       ;;                 (equal (alen1 ,dag-array-name dag-array)
       ;;                        (alen1 ,dag-parent-array-name dag-parent-array))

       ;;                 ,@hyps)
       ;;            (pseudo-dag-arrayp ,dag-array-name
       ;;                               (mv-nth ,dag-array-rv ,call)
       ;;                               (mv-nth ,dag-len-rv ,call)))
       ;;   :hints (("Goal" :in-theory (e/d (,fn)
       ;;                                   (pseudo-dag-arrayp
       ;;                                    bounded-dag-parent-arrayp
       ;;                                    natp
       ;;                                    index-in-bounds-after-expand-array))
       ;;            :cases ((< (car (dimensions ,dag-array-name dag-array)) '2147483646))
       ;;            :use (:instance index-in-bounds-after-expand-array
       ;;                            (name ,dag-array-name)
       ;;                            (l dag-array)
       ;;                            (index dag-len)))))
       )))

(defmacro def-dag-builder-theorems (call
                                    ret-spec ;should be a call to mv
                                    &key
                                    (dag-array-name 'nil)
                                    (dag-parent-array-name 'nil)
                                    (hyps 'nil)
                                    (hyps-everywhere 'nil)
                                    (hints 'nil)
                                    (recursivep 't)
                                    (expand 'nil)
                                    (dont-enable 'nil)
                                    )
  (def-dag-builder-theorems-fn call ret-spec dag-array-name dag-parent-array-name hyps hyps-everywhere hints recursivep expand dont-enable))
