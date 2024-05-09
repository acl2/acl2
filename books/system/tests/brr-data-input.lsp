; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; There are some calls of acl2-query that read from *standard-oi*.  So we
; redefine that input channel to be the current value of 'standard-oi.  There
; is also output printed to the comment window.  So we redirect that output to
; the current value of 'standard-co.

(defconst *old-standard-oi* *standard-oi*)
(redef+)
(make-event `(defconst *standard-oi* ',(standard-oi state)))
(make-event `(defconst *standard-co* ',(standard-co state)))
(redef-)

;;;;;;;;;;

(defstub f0 (x) t)

(defun f1 (x)
  (cons x x))

(defun f2 (x)
  (f1 (f0 x)))

(defun f3 (x)
  (if (atom x)
      (f2 x)
    (f2 (car x))))

(with-brr-data
 (thm (equal (f3 x)
             yyy)))

; Output is a bit painful to check and numes (i.e, the unique numbers
; corresponding to the rules) might change.
; (show-brr-data-lst (@ brr-data-lst))

(cw-gstack-for-term (cons (f0 (car x)) (f0 (car x))))

(cw-gstack-for-subterm* (f0 (car x)))
y

(cw-gstack-for-subterm* (f0 (car x)))
bad
?
n

; no results
(cw-gstack-for-term (f0 (car x)))

(cw-gstack-for-term* (:free (x) (cons x x)))
y
y

; error
(cw-gstack-for-term* (:free (y) (cons x x)))

; error
(cw-gstack-for-term* (:free x (cons x x)))

; error
(cw-gstack-for-term* (:free (x x) (cons x x)))

; error
(cw-gstack-for-term* (:free (x 3) (cons x x)))

; error
(cw-gstack-for-term* (:free (cons x x)))

; none
(cw-gstack-for-term (:free (v) (cons (f0 v) (f0 (car v)))))

(with-brr-data
 (thm (equal (f3 (f0 3))
             yyy)))

; Check that 3 above is translated to '3.
(cw-gstack-for-term (:free (x) (cons x x)))

; Check that 3 above is translated to '3.
(cw-gstack-for-subterm (f0 (car (f0 3))))

;;;;;;;;;;

(defstub g0 (x) t)

(defun g1 (x)
  (cons x x))

(defun g2 (x)
  (g1 (if (atom x)
          (g0 x)
        (g0 (car x)))))

(defun g3 (x)
  (g2 x))

(with-brr-data
 (thm (equal (g3 x)
             yyy)))

(cw-gstack-for-term (cons (g0 (car x)) (g0 (car x))))

; none
(cw-gstack-for-term (g0 (car x)))

(cw-gstack-for-subterm* (g0 (car x)))
y

(cw-gstack-for-subterm* (g0 (car x)))
n

(cw-gstack-for-subterm (cons (g0 (car x)) (g0 (car x))))

(with-brr-data
 (thm (implies (or (symbolp x) (consp x) (acl2-numberp x))
               (equal (g3 x)
                      yyy)))
 :global-var foo)

; It's perhaps a bit odd that we get the same result both times.  It's
; (I think) because rewrite-clause splits the first literal into cases before
; rewriting the g3 call, but we don't see that in the gstack.  The next example
; avoids that potential confusion.
(cw-gstack-for-term* (cons (g0 x) (g0 x))
; Test the :global-var option:
                     :global-var foo)
y
y

(cw-gstack-for-term* (cons (g0 x) (g0 x))
                     :global-var foo)
y
n

; The following makes it a little more clear what's going on when we issue
; cw-gstack-for-term*.
(with-brr-data
 (thm (implies (or (symbolp x) (consp x) (acl2-numberp x))
               (equal (g3 x)
                      yyy))
      :hints (("Goal"
               :in-theory (disable g3)
               :do-not '(preprocess))
              '(:in-theory (enable g3)))))

(cw-gstack-for-term* (cons (g0 x) (g0 x)))
y
y

(with-brr-data
 (thm (equal (append (f3 x) y)
             z)
      :hints (("Goal" :in-theory (disable append)))))

; None: (f3 x) rewrites to
;   (if (consp x)
;       (cons (f0 (car x)) (f0 (car x)))
;     (cons (f0 x) (f0 x)))
; so the rewriter never returns an append term.
; But we are searching for rewrite results.
(cw-gstack-for-subterm (append (cons (f0 (car x)) (f0 (car x))) y))

; Result:
(cw-gstack-for-subterm (cons (f0 (car x)) (f0 (car x))))

; One result:
(cw-gstack-for-subterm* (cons (f0 x) (f0 x)))
y

(include-book "kestrel/utilities/brr-data-all" :dir :system)
(set-brr-data-attachments all)

(with-brr-data
 (thm (equal (f3 x)
             (f3 y))))

(cw-gstack-for-subterm* (:free (v) (cons v v)))
y
y

;;; Test direct setting of gstackp to :brr-data.
(clear-brr-data-lst)
(f-put-global 'gstackp :brr-data state)
(thm (equal (f3 x)
            (f3 y)))
(set-brr-data-lst brr-data-lst)
(cw-gstack-for-subterm* (:free (v) (cons v v)))
y
y

;;;;;;;;;;

(redef+)
(defconst *standard-oi* *old-standard-oi*)
(redef-)

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)
