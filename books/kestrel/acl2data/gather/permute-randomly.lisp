; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(local
 (defthm len-revappend
     (equal (len (revappend x y))
            (+ (len x) (len y)))))

(local
 (defthm len-first-n-ac
     (implies (natp i)
              (equal (len (first-n-ac i lst ac))
                     (+ i (len ac))))))

(local (in-theory (enable natp-random$ random$-linear)))

(local
 (defthm len-nthcdr
     (equal (len (nthcdr n lst))
            (let ((n (nfix n)))
              (if (< n (len lst))
                  (- (len lst) n)
                  0)))))

(defun random$$ (limit state)
  (declare (type (integer 1 *) limit)
           (xargs :stobjs state))
  (if (and (f-boundp-global 'acl2data-testing state)
           (f-get-global 'acl2data-testing state))
      (mv 0 state)
    (random$ limit state)))

(defun permute-randomly-1 (lst k state)
  (declare (xargs :guard (and (true-listp lst)
                              (eql k (length lst)))
                  :stobjs state
                  :measure (len lst)))
  (cond ((or (endp lst)
             (not (mbt (and (true-listp lst)
                            (eql k (length lst))))))
         (mv nil state))
        (t (mv-let (n state)
             (random$$ k state)
             (mv-let (x state)
               (permute-randomly-1 (first-n-ac n lst (nthcdr (1+ n) lst))
                                   (1- k)
                                   state)
               (mv (cons (nth n lst)
                         x)
                   state))))))

(defun permute-randomly (lst state)

; Returns (mv lst' state') where lst' is a random permutation of lst.

  (declare (xargs :guard (true-listp lst)
                  :stobjs state))
  (if (null lst)
      (mv nil state)
    (permute-randomly-1 lst (length lst) state)))
