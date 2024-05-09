; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; See :DOC with-brr-data for general background on tracking rewrites.

; After including this book, all rewrites are tracked after first evaluating
; the following form.

;   (set-brr-data-attachments all)

; See also the related book, brr-data-failures.lisp, which tracks only failed
; rewrites.

; This book provides for brr-data collection that is similar to the default
; (which is described in :DOC brr-data-cw-gstack), but with the following two
; differences.

; (1) The built-in brr-data-cw-gstack collection method only collects top-level
;     rewriter calls, but brr-data-all has no such restriction.

; (2) The built-in brr-data-cw-gstack collection method collects only for
;     successful rewriter calls, but brr-data-all collects for all rewriter
;     calls.

(defun brkpt1-brr-data-entry-all (ancestors gstack rcnst state)

; The cw-gstack version of brr-data restricts collection to top-level rewriter
; calls.

  (declare (xargs :stobjs state)
           (ignore ancestors gstack rcnst state))
  t)

(defun brkpt2-brr-data-entry-all (ancestors gstack rcnst state)

; The cw-gstack version of brr-data restricts collection to top-level rewriter
; calls.

  (declare (xargs :stobjs state)
           (ignore ancestors gstack rcnst state))
  t)

(defun update-brr-data-1-all (lemma target unify-subst type-alist
                                    ancestors initial-ttree gstack rcnst
                                    pot-lst whs-data)

; This function is essentially identical to built-in function
; update-brr-data-1-cw-gstack.

  (declare (xargs :guard t))
  (let ((ctx 'update-brr-data-1-all))
    (cond
     ((listp whs-data)
      (let* ((pending (car whs-data))
             (completed (cdr whs-data)))
        (cons (cons (make brr-data
                          :pre (make brr-data-1
                                     :lemma lemma
                                     :target target
                                     :unify-subst unify-subst
                                     :type-alist type-alist
                                     :ancestors ancestors
                                     :initial-ttree initial-ttree
                                     :gstack gstack
                                     :rcnst rcnst
                                     :pot-list pot-lst)
                          :post nil
                          :completed nil)
                    pending)
              completed)))
     (t (er hard? ctx
            "Implementation error: Found whs-data not a listp:~|~x0"
            whs-data)))))

(defun update-brr-data-2-all (wonp failure-reason unify-subst gstack
                                   brr-result final-ttree rcnst ancestors
                                   whs-data)

; This function is essentially identical to built-in function
; update-brr-data-1-cw-gstack except that it takes the opposite action based on
; wonp.

  (declare (xargs :guard t)
           (ignore wonp ancestors))
  (let ((ctx 'update-brr-data-2-all))
    (cond
     ((listp whs-data)
      (let* ((pending (car whs-data))
             (completed (cdr whs-data)))
        (cond
         ((not (consp pending))
          (er hard? ctx
              "Implementation error: Found bad whs-data ((car pending) not a ~
               cons):~|~x0"
              whs-data))
         ((not (weak-brr-data-p (car pending)))
          (er hard? ctx
              "Implementation error: Found bad whs-data ((car pending) not a ~
               brr-data record)):~|~x0"
              whs-data))
         (t
          (let ((x (make brr-data-2
                         :failure-reason failure-reason
                         :unify-subst unify-subst
                         :gstack gstack
                         :brr-result brr-result
                         :final-ttree final-ttree
                         :rcnst rcnst)))
            (cond
             ((consp (cdr pending))
              (cond
               ((not (weak-brr-data-p (cadr pending)))
                (er hard? ctx
                    "Implementation error: Found whs-data (bad (cadr ~
                     pending)):~|~x0"
                    whs-data))
               (t

; Pop pending, folding (car pending) into the :completed field of (cadr
; pending), filling in the :post field of (car pending).  There is no change to
; completed.

                (cons (cons (change brr-data (cadr pending)
                                    :completed
                                    (cons (change brr-data (car pending)
                                                  :post x)
                                          (access brr-data (cadr pending)
                                                  :completed)))
                            (cddr pending))
                      completed))))
             (t

; Pop pending, leaving an empty stack.  So, we set the :post field of (car
; pending) to x and then push the resulting record onto completed.

              (cons nil
                    (cons (change brr-data (car pending)
                                  :post x)
                          completed)))))))))
     (t (er hard? ctx
            "Implementation error: Found whs-data not a listp:~|~x0"
            whs-data)))))

