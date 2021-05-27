; A meta rule for computing the length of a cons nest
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

(defevaluator lenconsev lenconsev-list
  ((len x) (cons a x) (BINARY-+ x y)))

;returns a new term and the number of conses skipped
(defun len-cons-meta-function-helper (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      (mv 0 term)
    (if (equal 'cons (car term))
        (mv-let (conses-skipped new-term)
                (len-cons-meta-function-helper (caddr term))
                (mv (+ 1 conses-skipped) new-term))
      (mv 0 term))))

(defun len-cons-meta-function (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (equal 'len (car term)) ;we don't get this for free, do we?
           )
      (mv-let (conses-skipped new-term)
;              (time$
              (len-cons-meta-function-helper (cadr term))
              ;)
              (if (zp conses-skipped)
                  term
                `(binary-+ ',conses-skipped (len ,new-term))))
    term))


(local
 (defthm helper
   (implies t ;(not (zp (CAR (LEN-CONS-META-FUNCTION-HELPER TERM3))))
            (equal (+ (car (len-cons-meta-function-helper term))
                      (len (lenconsev (mv-nth 1
                                              (len-cons-meta-function-helper term))
                                      alist)))
                   (len (lenconsev term alist))))))

;BBOZO does the whole RHS get rewritten after this fires?  does that slow things down?
(defthm len-cons-meta-rule
  (equal (lenconsev term alist)
         (lenconsev (len-cons-meta-function term) alist))
  :rule-classes ((:meta :trigger-fns (len))))
