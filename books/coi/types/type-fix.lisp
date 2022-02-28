;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")
(include-book "type-fty")
(include-book "kwargs")

(defun standard-fixing-rules (type-fix type-p signature)
  `(
    ,@(and signature `((def::signature ,type-fix (t) ,type-p)))
    
    (defthm ,(safe-packn-pos (list type-fix '- type-p) type-p)
      (implies
       (,type-p x)
       (equal (,type-fix x)
              x)))
    ))

(defun def-type-fix-fn (type-name args type-p type-fix define-fix type-fix! define-fix! type-witness open-default prefer-guarded non-executable disable signature in-theory)
  (let ((type-p    (default-name type-p    type-name '-p    type-name))
        (type-fix! (type-fix! type-fix! type-fix type-name type-p))
        (type-fix  (type-fix type-fix type-name type-fix! type-p))
        (preferred-fix (if prefer-guarded type-fix type-fix!))
        (alternate-fix (if prefer-guarded type-fix! type-fix))
        )
    (cond
     ((and define-fix define-fix!)
      (if (not type-witness)
          (hard-error 'def::type-fix "No fixing function ~x0 exists; you must provide a type witness using the :witness keyword" (acons #\0 type-name nil))
        `(encapsulate
             ()
           
           ,@(and in-theory `((local (in-theory ,in-theory))))

           (def::un ,type-fix! ,args
             (declare (xargs :signature ((t) ,type-p)
                             :signature-hints ((and acl2::stable-under-simplificationp
                                                    '(:in-theory (enable ,type-p))))))
             (let ((x ,@args))
               (if (,type-p x) x ,type-witness)))
        
           (acl2::defun-inline ,type-fix (x)
             (declare (xargs :guard (,type-p x)))
             (mbe :logic (,type-fix! x)
                  :exec  x))

           ,@(standard-fixing-rules preferred-fix type-p nil)

           (,@(if open-default '(defthm) '(defthmd)) ,(safe-packn-pos (list preferred-fix '-not- type-p) type-p)
            (implies
             (not (,type-p ,@args))
             (equal (,preferred-fix ,@args)
                    ,type-witness))
            :rule-classes ((:rewrite :backchain-limit-lst 0)))
           
           (defthm ,(safe-packn-pos (list alternate-fix '-to- preferred-fix) type-p)
             (equal (,alternate-fix x)
                    (,preferred-fix x)))
           
           ,@(and disable `((in-theory (disable ,type-fix ,type-fix!))))
           
           ,@(and non-executable `((in-theory (disable (,type-fix) (,type-fix!)))))
           
           )))
     ((and define-fix (not define-fix!))
      `(encapsulate
           ()
         ,@(and in-theory `((local (in-theory ,in-theory))))
         ,@(standard-fixing-rules type-fix! type-p signature)
         (acl2::defun-inline ,type-fix (x)
           (declare (xargs :guard (,type-p x)))
           (mbe :logic (,type-fix! x)
                :exec  x))
         ,@(and non-executable `((in-theory (disable (,type-fix)))))
         ,@(and disable `((in-theory (disable ,type-fix!))))
         ))
     ((and define-fix! (not define-fix))
      `(encapsulate
           ()
         ,@(and in-theory `((local (in-theory ,in-theory))))
         ,@(standard-fixing-rules type-fix type-p signature)
         (defun ,type-fix! (x)
           (declare (type t x))
           (with-guard-checking :none (ec-call (,type-fix x))))
         ,@(and non-executable `((in-theory (disable (,type-fix!)))))
         ,@(and disable `((in-theory (disable ,type-fix))))
         ))
     (t ;; Both fixers already exist (?)
      (let ((zed (cw "~%Both fixing functions already exist for type ~x0; doing nothing~%" (acons #\0 type-name nil))))
        (declare (ignore zed))
        `(encapsulate
             ()
           ,@(and in-theory `((local (in-theory ,in-theory))))
           ,@(standard-fixing-rules type-fix type-p signature)
           ,@(standard-fixing-rules type-fix! type-p signature)
           ,@(and disable `((in-theory (disable ,type-fix! ,type-fix))))
           )))
     )))

(set-state-ok t)

(defun def-type-fix-wrapper (type-name args type-p type-fix type-fix! type-witness open-default prefer-guarded non-executable disable signature in-theory state)
  (let* ((define-fix  (undefined-fn type-fix))
         (define-fix! (undefined-fn type-fix!)))
    (def-type-fix-fn type-name args type-p type-fix define-fix type-fix! define-fix! type-witness open-default prefer-guarded non-executable disable signature in-theory)))

(defmacro def::type-fix (type-name &rest kvlist)
  (b* ((kwargs (kwargs (def-type-fix-keywords) kvlist))
       ((&key args type-p fix fix! type-witness open-fix-default prefer-guarded non-executable disable-fix fix-signature fix-in-theory) kwargs)
       )
    `(make-event
      (def-type-fix-wrapper ',type-name ',args ',type-p ',fix ',fix!
        ',type-witness ',open-fix-default ',prefer-guarded
        ',non-executable ',disable-fix ',fix-signature ',fix-in-theory
        state)
      )))

(local
 (def::type-fix natural
   :args (x)
   :type-p natp
   :fix    n-fix
   :fix!   nat-fix!
   :type-witness 0
   :open-fix-default nil
   :prefer-guarded t
   :non-executable t
   :fix-in-theory nil
   :fix-signature t
   :disable-fix t
   )
 )
