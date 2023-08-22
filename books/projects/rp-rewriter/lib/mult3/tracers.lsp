

(in-package "RP")

;; (ld "projects/rp-rewriter/lib/mult3/tracers.lsp" :dir :system)

(include-book "projects/rp-rewriter/lib/mult3/svtv-top" :dir :system)

(clear-memoize-tables)

(clear-memoize-statistics)

(hons-clear t)

(memoize 'ordered-s/c-p)

;; (unpack-booth-later-enabled)

(define pp-lst-flattened-p (pp-lst)
  (if (atom pp-lst)
      (equal pp-lst nil)
    (b* ((e (car pp-lst))
         (e (ex-from-rp/times e)))
      (and (not (binary-fnc-p e))
           (pp-lst-flattened-p (cdr pp-lst))))))


(trace$
 (extract-equals-from-pp-lst
  :cond (or (equal acl2::traced-fn 'extract-equals-from-pp-lst)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list res-pp-lst)
                acl2::values)
               ((list pp-lst &)
                acl2::arglist)
               )
            (if (and (pp-lst-orderedp res-pp-lst)
                     (or (unpack-booth-later-enabled)
                         (pp-lst-flattened-p res-pp-lst)))
                (msg "")
              (msg  "---Not ordered from extract-equals-from-pp-lst:~%--Inputs: pp-lst ~x0.~%--Rturned: ~%res-pp-lst: ~x1"
                   (list (pp-lst-orderedp pp-lst) pp-lst)
                   (list (pp-lst-orderedp res-pp-lst) res-pp-lst)
                   ))))))

(trace$
 (extract-from-equals-lst
  :cond (or (equal acl2::traced-fn 'extract-from-equals-lst)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s res-pp-lst c-lst changed)
                acl2::values)
               ((list pp-lst)
                acl2::arglist)
               (s-lst (list-to-lst s)))
            (if (or (not changed)
                    (and (ordered-s/c-p-lst s-lst)
                         (pp-lst-orderedp res-pp-lst)

                         (or (unpack-booth-later-enabled)
                             (pp-lst-flattened-p res-pp-lst))
                     
                         (ordered-s/c-p-lst c-lst)))
                (msg "")
              (msg  "---Not ordered from extract-from-equals-lst:~%--Inputs: pp-lst ~x0.~%--Rturned: ~%s-lst: ~x1.~%pp-lst:~x2.~%c-lst:~x3.~%"
                   (list (pp-lst-orderedp pp-lst) pp-lst)
                   (list (ordered-s/c-p-lst s-lst) s-lst)
                   (list (pp-lst-orderedp res-pp-lst) res-pp-lst)
                   (list (ordered-s/c-p-lst c-lst) c-lst)
                   ))))))

(trace$
 (new-sum-merge
  :cond (or (equal acl2::traced-fn 'new-sum-merge)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s pp-lst c-lst)
                acl2::values)
               (s-lst (list-to-lst s))
               ((list term)
                acl2::arglist))
            (if (and (ordered-s/c-p-lst s-lst)
                     (pp-lst-orderedp pp-lst)
                     (ordered-s/c-p-lst c-lst))
                (msg "")
              (msg  "---Not ordered from new-sum-merge:~%--Inputs: term: ~x0.~%--Rturned: ~%s-lst: ~x1.~%pp-lst:~x2.~%c-lst:~x3.~%"
                   term
                   (list (ordered-s/c-p-lst s-lst) s-lst)
                   (list (pp-lst-orderedp pp-lst) pp-lst)
                   (list (ordered-s/c-p-lst c-lst) c-lst)
                   ))))))



(trace$
 (pp-sum-sort-lst
  :cond (or (equal acl2::traced-fn 'pp-sum-sort-lst)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list res-pp-lst)
                acl2::values)
               ((list pp-lst)
                acl2::arglist))
            (if (pp-lst-orderedp res-pp-lst)
                (msg "")
              (msg "---Not ordered from pp-sum-sort-lst: ~%--Inputs: pp-lst: ~x0. ~%--Returned: res-pp-lst: ~x1.~%"
                   (list `(:pp-order ,(pp-lst-orderedp pp-lst))
                         pp-lst)
                   (list ``(:pp-order ,(pp-lst-orderedp res-pp-lst))
                         res-pp-lst)))))))

(trace$
 (s-fix-pp-args-aux
  :cond (or (equal acl2::traced-fn 's-fix-pp-args-aux)) ;; Don't want to see *1* functions
  :entry (:fmt! (b* (((list pp-lst) acl2::arglist))
                  (if (or (ordered-s/c-p-lst pp-lst)
                          (pp-lst-orderedp pp-lst))
                      (msg "")
                    (msg "---Not ordered input to s-fix-pp-args-aux: ~%--Inputs: pp-lst: ~x0.~%"
                         (list `((:pp-order ,(pp-lst-orderedp pp-lst))
                                 (:s/c-order ,(ordered-s/c-p-lst pp-lst)))
                               pp-lst)))))
  :exit  (:fmt!
          (b* (((list cleaned-pp-lst)
                acl2::values)
               ((list pp-lst)
                acl2::arglist))
            (if (or (ordered-s/c-p-lst cleaned-pp-lst)
                    (pp-lst-orderedp cleaned-pp-lst))
                (msg "")
              (msg "---Not ordered from s-fix-pp-args-aux: ~%--Inputs: pp-lst: ~x0. ~%--Returned: cleaned-pp-lst: ~x1.~%"
                   (list `((:pp-order ,(pp-lst-orderedp pp-lst))
                           (:s/c-order ,(ordered-s/c-p-lst pp-lst)))
                         pp-lst)
                   (list `((:pp-order ,(pp-lst-orderedp cleaned-pp-lst))
                          (:s/c-order ,(ordered-s/c-p-lst cleaned-pp-lst)))
                         cleaned-pp-lst)))))))

(trace$
 (s-spec-meta-aux
  :cond (or (equal acl2::traced-fn 's-spec-meta-aux)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list res)
                acl2::values)
               ((list s pp-lst c-lst)
                acl2::arglist)
               (s-lst (list-to-lst s)))
            (if (and (ordered-s/c-p res)
                     (ordered-s/c-p-lst s-lst)
                     (pp-lst-orderedp pp-lst)
                     (ordered-s/c-p-lst c-lst))
                (msg "")
              (msg "---Not ordered from s-spec-meta-aux:~%--Inputs: s-lst: ~x0.~%pp-lst:~x1.~%c-lst:~x2.~%--Returned: res: ~x3.~%"
                   (list (ordered-s/c-p-lst s-lst) s-lst)
                   (list (pp-lst-orderedp pp-lst) pp-lst)
                   (list (ordered-s/c-p-lst c-lst) c-lst)
                   (list (ordered-s/c-p res) res)))))))


(trace$
 (cross-product-two-larges-aux-pp-lst
  :cond (or (equal acl2::traced-fn 'cross-product-two-larges-aux-pp-lst)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list res-s-lst res-pp-lst res-c-lst valid)
                acl2::values)
               ((list pp-lst single-s/c2)
                acl2::arglist))
            (if (and valid
                     (ordered-s/c-p-lst res-s-lst)
                     (pp-lst-orderedp res-pp-lst)
                     (ordered-s/c-p-lst res-c-lst))
                (msg "")
              (msg "---Not ordered from cross-product-two-larges-aux-pp-lst: ~%--Inputs: pp-lst: ~x0.~%single-s/c2:~x1. ~%--Returned: res-s-lst: ~x2, res-pp-lst: ~x3, res-c-lst: ~x4.~%"
                   (list (pp-lst-orderedp pp-lst) pp-lst)
                   (list (ordered-s/c-p single-s/c2) single-s/c2)
                   
                   (list (ordered-s/c-p-lst res-s-lst) res-s-lst)
                   (list (pp-lst-orderedp res-pp-lst) res-pp-lst)
                   (list (ordered-s/c-p-lst res-c-lst) res-c-lst)
                   ))))))


(trace$
 (s-of-s-fix-lst
  :cond (or (equal acl2::traced-fn 's-of-s-fix-lst)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list pp-res-lst c-res-lst)
                acl2::values)
               ((list s-lst pp-lst c-lst)
                acl2::arglist))
            (if (and (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (progn$
               (msg "---Not ordered from s-of-s-fix-lst:~%--Inputs: s-lst: ~x0.~%pp-lst:~x1.~%c-lst:~x2.~%--Returned: pp-res-lst: ~x3.~%c-res-lst: ~x4 . ~% ~$"
                   (list (and (ordered-s/c-p-lst s-lst) :s-lst-ok) s-lst)
                   (list (and (pp-lst-orderedp pp-lst) :pp-lst-ok) pp-lst)
                   (list (and (ordered-s/c-p-lst c-lst) :c-lst-ok) c-lst)
                   (list (and (pp-lst-orderedp pp-res-lst) :pp-res-lst-ok) pp-res-lst)
                   (list (and (ordered-s/c-p-lst c-res-lst) :c-res-lst-ok) c-res-lst))
               ;;(break$)
               ))))))

(trace$
 (pp-sum-merge-aux
  :cond (or (equal acl2::traced-fn 's-of-s-fix-lst)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list pp-res-lst c-res-lst)
                acl2::values)
               ((list pp1-lst pp2-lst)
                acl2::arglist))
            (if (and (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (progn$
               (msg "---Not ordered from s-of-s-fix-lst:~%--Inputs: s-lst: ~x0.~%pp-lst:~x1.~%c-lst:~x2.~%--Returned: pp-res-lst: ~x3.~%c-res-lst: ~x4 . ~% ~$"
                   (if (ordered-s/c-p-lst s-lst) :s-lst-ok s-lst)
                   (if (pp-lst-orderedp pp-lst) :pp-lst-ok pp-lst)
                   (if (ordered-s/c-p-lst c-lst) :c-lst-ok c-lst)
                   (if (pp-lst-orderedp pp-res-lst) :pp-res-lst-ok pp-res-lst)
                   (if (ordered-s/c-p-lst c-res-lst) :c-res-lst-ok c-res-lst))
               ;;(break$)
               ))))))



(trace$
 (s-c-spec-meta
  :cond (or (equal acl2::traced-fn 's-c-spec-meta)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list res-term ?dont-rw)
                acl2::values))
            (cond ((and 
                        (not (or (and (equal (caar acl2::arglist) 's-c-spec)
                                      (ordered-s/c-p (cadr res-term))
                                      (ordered-s/c-p (cadr (caddr res-term))))
                                 (and (equal (caar acl2::arglist) 's-spec)
                                      (ordered-s/c-p res-term))
                                 (and (equal (caar acl2::arglist) 'c-spec)
                                      (ordered-s/c-p res-term)))))
                   (msg "---Not ordered from s-c-spec-meta Input:
  ~x0. res-term: ~x1. ~% ~$"
                        acl2::arglist res-term))
                  ((or (and (equal (caar acl2::arglist) 's-c-spec)
                            (or (s/c-has-times (cadr res-term))
                                (s/c-has-times (cadr (caddr res-term)))))
                       (and (equal (caar acl2::arglist) 's-spec)
                            (s/c-has-times res-term))
                       (and (equal (caar acl2::arglist) 'c-spec)
                            (s/c-has-times res-term)))
                   (msg "---bad times from s-c-spec-meta Input:
  ~x0. res-term: ~x1. ~% ~$"
                        acl2::arglist res-term))
                  (t 
                   (msg ""))))
              )))


(trace$
 (unpack-booth-for-s*
  :cond (or (equal acl2::traced-fn 'unpack-booth-for-s*)
            (equal acl2::traced-fn 'unpack-booth-for-s-fn));; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from unpack-booth-for-s*. Input:
  ~x0. s-res-lst: ~x1. pp-res-lst: ~x2. c-res-lst: ~x3 ~%"
                   acl2::arglist s-res-lst pp-res-lst c-res-lst))))))

(trace$
 (unpack-booth-for-c*
  :cond (or (equal acl2::traced-fn 'unpack-booth-for-c*)
            (equal acl2::traced-fn 'unpack-booth-for-c-fn));; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from unpack-booth-for-c* Input:
  ~x0. s-res-lst: ~x1. pp-res-lst: ~x2. c-res-lst: ~x3 ~%"
                   acl2::arglist s-res-lst pp-res-lst
                   c-res-lst))))))

(trace$
 (unpack-booth-for-c-lst-fn
  :cond (or (equal acl2::traced-fn 'unpack-booth-for-c-lst-fn)
            (equal acl2::traced-fn 'unpack-booth-for-c-lst*));; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from unpack-booth-for-c-lst Input:
  ~x0 (ordered:~x1). Output vals: s-res-lst: ~x2. pp-res-lst: ~x3. c-res-lst: ~x4 ~%"
                   acl2::arglist (ordered-s/c-p-lst (car acl2::arglist))

                   s-res-lst pp-res-lst c-res-lst))))))

(trace$
 (unpack-booth-for-c-lst*
  :cond (or (equal acl2::traced-fn 'unpack-booth-for-c-lst-fn)
            (equal acl2::traced-fn 'unpack-booth-for-c-lst*));; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from unpack-booth-for-c-lst* Input:
  ~x0 (ordered:~x1). Output vals: s-res-lst: ~x2. pp-res-lst: ~x3. c-res-lst: ~x4 ~%"
                   acl2::arglist (ordered-s/c-p-lst (car acl2::arglist))

                   s-res-lst pp-res-lst c-res-lst))))))

(trace$
 (unpack-booth-process-pp-arg*
  :cond (or (equal acl2::traced-fn 'unpack-booth-process-pp-arg*)
            (equal acl2::traced-fn 'unpack-booth-process-pp-arg-fn)) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from unpack-booth-process-pp-arg* Input:
  ~x0. s-res-lst: ~x1. pp-res-lst: ~x2. c-res-lst: ~x3 ~%"
                   acl2::arglist s-res-lst pp-res-lst
                   c-res-lst))))))


(trace$
 (unpack-booth-process-pp-arg-fn
  :cond (equal acl2::traced-fn 'unpack-booth-process-pp-arg-fn) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (ordered-s/c-p-lst c-res-lst)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from unpack-booth-process-pp-arg Input:
  ~x0 (ordered:~x1). s-res-lst: ~x2. pp-res-lst: ~x3. c-res-lst: ~x4 ~%"
                   acl2::arglist
                   (pp-orderedp (car acl2::arglist))
                   
                   s-res-lst pp-res-lst c-res-lst))))))


(trace$
 (pp-sum-merge-lst-for-s
  :cond (equal acl2::traced-fn 'pp-sum-merge-lst-for-s) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list pp-res-lst) acl2::values))
            (if (pp-lst-orderedp pp-res-lst)
                (msg "")
              (msg "---Not ordered from pp-sum-merge-lst-for-s Input:
  ~x0 (ordered:~x1 ). pp-res-lst: ~x2. ~%"
                   acl2::arglist
                   (list (pp-lst-orderedp (car acl2::arglist))
                         (pp-lst-orderedp (cadr acl2::arglist)))
                   
                   pp-res-lst))))))


(trace$
 (unpack-booth-buried-in-pp-lst-fn
  :cond (equal acl2::traced-fn 'unpack-booth-buried-in-pp-lst-fn) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list pp-res-lst) acl2::values))
            (if (pp-lst-orderedp pp-res-lst)
                (msg "")
              (msg "---Not ordered from unpack-booth-buried-in-pp-lst-fn Input:
  ~x0 (ordered:~x1 ). pp-res-lst: ~x2. ~%"
                   acl2::arglist
                   (pp-lst-orderedp (car acl2::arglist))
                   
                   pp-res-lst))))))

(trace$
 (unpack-booth-for-pp-lst
  :cond (equal acl2::traced-fn 'unpack-booth-for-pp-lst) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list pp-res-lst) acl2::values))
            (if (pp-lst-orderedp pp-res-lst)
                (msg "")
              (msg "---Not ordered from unpack-booth-for-pp-lst Input:
  ~x0 (ordered:~x1 ). pp-res-lst: ~x2. ~%"
                   acl2::arglist
                   (pp-lst-orderedp (car acl2::arglist))
                   
                   pp-res-lst))))))


(trace$
 (ex-from-pp-lst
  :cond (equal acl2::traced-fn 'ex-from-pp-lst) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (list-of-only-s/c-p s-res-lst 's)
                     (ordered-s/c-p-lst c-res-lst)
                     (list-of-only-s/c-p c-res-lst 'c)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from ex-from-pp-lst Input:
  ~x0 (ordered:~x1). s-res-lst: ~x2. pp-res-lst: ~x3. c-res-lst: ~x4 ~%"
                   acl2::arglist
                   (pp-lst-orderedp (car acl2::arglist))
                   
                   s-res-lst pp-res-lst c-res-lst))))))

(trace$
 (pp-radix8+-fix
  :cond (equal acl2::traced-fn 'pp-radix8+-fix) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (list-of-only-s/c-p s-res-lst 's)
                     (ordered-s/c-p-lst c-res-lst)
                     (list-of-only-s/c-p c-res-lst 'c)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from pp-radix8+-fix:
Input: ~x0 (ordered:~x1).
s-res-lst:~%~x2 (ordered: ~x3).
pp-res-lst:~%~x4 (ordered: ~x5).
c-res-lst:~%~x6 (ordered: ~x7)~%~%"
                   acl2::arglist
                   (pp-lst-orderedp (car acl2::arglist))
                   
                   s-res-lst (list (s-sum-ordered-listp s-res-lst) (ordered-s/c-p-lst s-res-lst))
                   pp-res-lst (pp-lst-orderedp pp-res-lst)
                   c-res-lst (list (s-sum-ordered-listp c-res-lst)
                                   (ordered-s/c-p-lst c-res-lst))))))))

(trace$
 (pp-radix8+-fix-aux-for-s/c
  :cond (equal acl2::traced-fn 'pp-radix8+-fix-aux-for-s/c) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst ?valid)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (list-of-only-s/c-p s-res-lst 's)
                     (ordered-s/c-p-lst c-res-lst)
                     (list-of-only-s/c-p c-res-lst 's)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from pp-radix8+-fix-aux-for-s/c
Input: ~x0 (ordered:~x1).
s-res-lst:~%~x2 (ordered: ~x3).
pp-res-lst:~%~x4 (ordered: ~x5).
c-res-lst:~%~x6 (ordered: ~x7)
Valid:~x8~%~%"
                   acl2::arglist
                   (ordered-s/c-p (car acl2::arglist))
                   
                   s-res-lst (list (s-sum-ordered-listp s-res-lst) (ordered-s/c-p-lst s-res-lst))
                   pp-res-lst (pp-lst-orderedp pp-res-lst)
                   c-res-lst (list (s-sum-ordered-listp c-res-lst) (ordered-s/c-p-lst c-res-lst))
                   valid))))))

(trace$
 (pp-radix8+-fix-aux-for-s/c
  :cond (equal acl2::traced-fn 'pp-radix8+-fix-aux-for-s/c) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst ?valid)
                acl2::values))
            (if (and (ordered-s/c-p-lst s-res-lst)
                     (list-of-only-s/c-p s-res-lst 's)
                     (ordered-s/c-p-lst c-res-lst)
                     (list-of-only-s/c-p c-res-lst 'c)
                     (pp-lst-orderedp pp-res-lst))
                (msg "")
              (msg "---Not ordered from pp-radix8+-fix-aux-for-s/c
Input: ~x0 (ordered:~x1).
s-res-lst:~%~x2 (ordered: ~x3).
pp-res-lst:~%~x4 (ordered: ~x5).
c-res-lst:~%~x6 (ordered: ~x7)
Valid:~x8~%~%"
                   acl2::arglist
                   (ordered-s/c-p (car acl2::arglist))
                   
                   s-res-lst (list (s-sum-ordered-listp s-res-lst) (ordered-s/c-p-lst s-res-lst))
                   pp-res-lst (pp-lst-orderedp pp-res-lst)
                   c-res-lst (list (s-sum-ordered-listp c-res-lst) (ordered-s/c-p-lst c-res-lst))
                   valid))))))


(trace$
 (create-c-instance
  :cond (equal acl2::traced-fn 'create-c-instance) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values)

               ((list s-lst pp-lst c-lst)
                acl2::arglist)
               )
            (cond ((and 
                        (not (and (ordered-s/c-p-lst s-res-lst)
                             (list-of-only-s/c-p s-res-lst 's)
                             (ordered-s/c-p-lst c-res-lst)
                             (list-of-only-s/c-p c-res-lst 'c)
                             (pp-lst-orderedp pp-res-lst))))
                   (msg "--- not ordered from create-c-instance ~%Inputs: ~%s-lst:~%~x0 ~%pp-lst:~%~x1 ~%c-lst:~%~x2 
Outputs: ~$s-res-lst:~%~x3 ~%pp-res-lst:~%~x4 ~%c-res-lst:~%~x5 ~%~%"
                        (let* ((o1 (s-sum-ordered-listp s-lst))
                               (o2 (ordered-s/c-p-lst s-lst)))
                          (if (and o1 o2) :ordered (list s-lst :self o1 :children o2)))

                        (let* ((o1 (pp-lst-orderedp pp-res-lst)))
                          (if o1 :ordered (list pp-lst :not-ordered)))

                        (let* ((o1 (s-sum-ordered-listp c-lst))
                               (o2 (ordered-s/c-p-lst c-lst)))
                          (if (and o1 o2) :ordered (list c-lst :self o1 :children o2)))
                   
                        (let* ((o1 (s-sum-ordered-listp s-res-lst))
                               (o2 (ordered-s/c-p-lst s-res-lst)))
                          (if (and o1 o2) :ordered (list s-res-lst :self o1 :children o2)))

                        (let* ((o1 (pp-lst-orderedp pp-res-lst)))
                          (if o1 :ordered (list pp-res-lst :not-ordered)))

                        (let* ((o1 (s-sum-ordered-listp c-res-lst))
                               (o2 (ordered-s/c-p-lst c-res-lst)))
                          (if (and o1 o2) :ordered (list c-res-lst :self o1 :children o2)))))
                  ((or ;; (loop$ for x in s-res-lst thereis (times-p x))
                    ;; (loop$ for x in pp-res-lst thereis (times-p x))
                    ;; (loop$ for x in c-res-lst thereis (times-p x))

                    (and (or (s/c-has-times-lst c-res-lst)
                             (s/c-has-times-lst s-res-lst))
                         ;;(not (s/c-has-times `(c '0 (list . ,s-lst) (list . ,pp-lst) (list . ,c-lst))))
                         ))
                   (msg "---Times instance from create-c-instance ~%
Inputs:
s-lst:~% ~x0
pp-lst:~% ~x1
c-lst:~% ~x2 
Outputs:
s-res-lst:~%~x3 ~%pp-res-lst:~%~x4 ~%c-res-lst:~%~x5 ~%~%~$"
                        s-lst pp-lst c-lst s-res-lst pp-res-lst c-res-lst
                        ;; (let* ((o1 (loop$ for x in s-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list s-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in pp-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list pp-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in c-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list c-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in s-res-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list s-res-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in pp-res-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list pp-res-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in c-res-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list c-res-lst :has-times)))
                        ))
                  (t 
                   (msg "")))))
  ))

(trace$
 (create-s-instance
  :cond (equal acl2::traced-fn 'create-s-instance) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values)

               ((list pp c)
                acl2::arglist)
               (c-lst (list-to-lst c))
               (pp-lst (list-to-lst pp))
               )
            (cond ((and 
                        (not (and (ordered-s/c-p-lst s-res-lst)
                             (list-of-only-s/c-p s-res-lst 's)
                             (ordered-s/c-p-lst c-res-lst)
                             (list-of-only-s/c-p c-res-lst 'c)
                             (pp-lst-orderedp pp-res-lst))))
                   (msg "--- not ordered from create-s-instance ~%Inputs: ~%pp-lst:~%~x0 ~%c-lst:~%~x1
Outputs: ~$s-res-lst:~%~x2 ~%pp-res-lst:~%~x3 ~%c-res-lst:~%~x4 ~%~%"

                        (let* ((o1 (pp-lst-orderedp pp-res-lst)))
                          (if o1 :ordered (list pp-lst :not-ordered)))

                        (let* ((o1 (s-sum-ordered-listp c-lst))
                               (o2 (ordered-s/c-p-lst c-lst)))
                          (if (and o1 o2) :ordered (list c-lst :self o1 :children o2)))
                   
                        (let* ((o1 (s-sum-ordered-listp s-res-lst))
                               (o2 (ordered-s/c-p-lst s-res-lst)))
                          (if (and o1 o2) :ordered (list s-res-lst :self o1 :children o2)))

                        (let* ((o1 (pp-lst-orderedp pp-res-lst)))
                          (if o1 :ordered (list pp-res-lst :not-ordered)))

                        (let* ((o1 (s-sum-ordered-listp c-res-lst))
                               (o2 (ordered-s/c-p-lst c-res-lst)))
                          (if (and o1 o2) :ordered (list c-res-lst :self o1 :children o2)))))
                  ((or ;; (loop$ for x in s-res-lst thereis (times-p x))
                    ;; (loop$ for x in pp-res-lst thereis (times-p x))
                    ;; (loop$ for x in c-res-lst thereis (times-p x))

                    (and (or (s/c-has-times-lst c-res-lst)
                             (s/c-has-times-lst s-res-lst))
                         ;;(not (s/c-has-times `(c '0 (list . ,s-lst) (list . ,pp-lst) (list . ,c-lst))))
                         ))
                   (msg "---Times instance from create-s-instance ~% Inputs had it? :~x0
Inputs:
pp-lst:~% ~x1
c-lst:~% ~x2
Outputs:
s-res-lst:~%~x3 ~%pp-res-lst:~%~x4 ~%c-res-lst:~%~x5 ~%~%
~$" ;; throw an error.
                        (s/c-has-times `(s '0 (list . ,pp-lst) (list . ,c-lst)))
                         pp-lst c-lst s-res-lst pp-res-lst c-res-lst
                        ))
                  (t 
                   (msg "")))))
  ))

(trace$
 (c-pattern1-reduce
  :cond (equal acl2::traced-fn 'c-pattern1-reduce) ;; Don't want to see *1* functions
  :entry (:fmt! (msg ""))
  :exit  (:fmt!
          (b* (((list s-res-lst pp-res-lst c-res-lst)
                acl2::values)

               ((list s-lst pp-lst c-lst)
                acl2::arglist)
               )
            (cond ((and (or (s/c-has-times-lst c-res-lst)
                            (s/c-has-times-lst s-res-lst))
                        (not (s/c-has-times `(c '0 (list . ,s-lst) (list . ,pp-lst) (list . ,c-lst))))
                        )
                   (msg "---Times instance from c-pattern1-reduce ~%
Inputs:
s-lst:~% ~x0
pp-lst:~% ~x1
c-lst:~% ~x2 
Outputs:
s-res-lst:~%~x3 ~%pp-res-lst:~%~x4 ~%c-res-lst:~%~x5 ~%~%"
                        s-lst pp-lst c-lst s-res-lst pp-res-lst c-res-lst
                        ;; (let* ((o1 (loop$ for x in s-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list s-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in pp-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list pp-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in c-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list c-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in s-res-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list s-res-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in pp-res-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list pp-res-lst :has-times)))
                        ;; (let* ((o1 (loop$ for x in c-res-lst thereis (times-p x))))
                        ;;   (if (and o1) :good (list c-res-lst :has-times)))
                        ))
                  (t 
                   (msg "")))))
            ))


(clear-memoize-statistics) (clear-memoize-tables)

(rp::show-rules :cnt)

(progn
  (profile 'rp::create-c-instance)
  (profile 'rp::create-s-instance)
  (profile 'rp::create-s-c-res-instance)
  
  (profile 'rp::sum-merge-lst-for-s)
  (profile 'rp::pp-sum-merge-aux)

  (profile 'rp::extract-equals-from-pp-lst)

  (profile 'rp::cross-product-pp-aux-for-pp-lst)

  (profile 'rp::extract-equals-from-pp-lst-aux)
  
  (profile 'SVL::CONCAT-META)
  (profile 'SVL::BITS-OF-META-FN)
  (profile 'SVL::4VEC-RSH-OF-META)
  (profile 'rp::rp-rw-rule)
  (profile 'rp::rp-rw-rule-aux)
  (profile 'rp::rp-rw-meta-rule-main)
  (profile 'rp::s-c-spec-meta)
  (profile 'rp::preprocess-then-rp-rw)
  (profile 'rp::unpack-booth-meta)
  (profile 'rp::hons-copy2)
  (profile 'rp::pp-flatten-fn)
  (profile 'rp::unpack-booth-general-meta$)
  (profile 'rp::unpack-booth-general-postprocessor)
  ;;(profile 'rp::pp-radix8+-fix)
  (profile 'rp::ex-from-pp-lst)
  (profile 'rp::c-of-s-fix-lst)
  (profile 'rp::maybe-bitp-precheck)
  (profile 'rp::c-pattern1-reduce)
  (profile 'rp::new-sum-merge)
  (profile 'rp::c-pattern2-reduce)
  (profile 'rp::c-pattern0-reduce)

  (profile 'rp::4vec-branch-drop-r-case)

  (profile 'rp::rp-equal-iter-pp+-meta)

  (profile 'rp::pp-lst-orderedp)
  (profile 'rp::pp-sum-sort-lst)
  ;;(profile 'rp::pp-radix8+-fix-aux-for-s/c-main)
  (profile 'rp::recollect-pp-lst-to-sc)

  (profile 'rp::calculate-c-hash)

  (profile 'rp::sort-sum-meta)

  ;;(profile 'rp::sort-pp-lists)

  (profile 'rp::sort-sum-meta-aux2)

  (profile 'rp::pp-term-to-pp-e-list)
  (profile 'rp::merge-sorted-pp-e-lists)

  (profile 'rp::s-c-spec-meta)
  
  )


(progn
  (profile 'rp::pp-flatten-fn)
  
  
  ;;(profile 'and$-pp-lists)
  ;;(profile 'and$-pp-lists-aux)
  )
