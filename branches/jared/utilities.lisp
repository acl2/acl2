; ACL2 Version 6.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2014, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

(defun remove1-by-position (target-index lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc)
                              (natp target-index)
                              (< target-index (len lst)))))
  (cond
   ((zp target-index)
    (revappend acc (cdr lst)))
   (t (remove1-by-position (1- target-index) (cdr lst) (cons (car lst) acc)))))

(defun all-equal (x lst)
  (declare (xargs :guard t))
  (cond ((atom lst) t)
        (t (and (equal x (car lst))
                (all-equal x (cdr lst))))))

(defun alist-keys-subsetp (x keys)
  (cond ((endp x) t)
        ((member-eq (caar x) keys)
         (alist-keys-subsetp (cdr x) keys))
        (t nil)))

(defun merge-symbol-alistp (a1 a2)
  (cond ((endp a1) a2)
        ((endp a2) a1)
        ((symbol-< (caar a1) (caar a2))
         (cons (car a1)
               (merge-symbol-alistp (cdr a1) a2)))
        (t
         (cons (car a2)
               (merge-symbol-alistp a1 (cdr a2))))))

(defun merge-sort-symbol-alistp (alist)
  (cond ((endp (cdr alist)) alist)
        ((endp (cddr alist))
         (cond ((symbol-< (car (car alist)) (car (cadr alist)))
                alist)
               (t (list (cadr alist) (car alist)))))
        (t (let* ((n (length alist))
                  (a (ash n -1)))
             (merge-symbol-alistp
              (merge-sort-symbol-alistp (take a alist))
              (merge-sort-symbol-alistp (nthcdr a alist)))))))

(mutual-recursion

(defun all-vars-boundp (term alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-alistp alist))))
  (cond ((variablep term)
         (assoc-eq term alist))
        ((fquotep term) t)
        (t (all-vars-lst-boundp (fargs term) alist))))

(defun all-vars-lst-boundp (lst alist)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-alistp alist))))
  (cond ((endp lst) t)
        (t (and (all-vars-boundp (car lst) alist)
                (all-vars-lst-boundp (cdr lst) alist)))))

)

(mutual-recursion

(defun dumb-occur (x y)

; This function determines if term x occurs in term y, but does not
; look for x inside of quotes.  It is thus equivalent to occur if you
; know that x is not a quotep.

  (cond ((equal x y) t)
        ((variablep y) nil)
        ((fquotep y) nil)
        (t (dumb-occur-lst x (fargs y)))))

(defun dumb-occur-lst (x lst)
  (cond ((null lst) nil)
        (t (or (dumb-occur x (car lst))
               (dumb-occur-lst x (cdr lst))))))

)

(defun all-dumb-occur-lst (args cl)
  (cond ((endp args) t)
        (t (and (dumb-occur-lst (car args) cl)
                (all-dumb-occur-lst (cdr args) cl)))))


(mutual-recursion

(defun dumb-occur-var (var term)

; This function determines if variable var occurs in the given term.  This is
; the same as dumb-occur, but optimized for the case that var is a variable.

  (cond ((eq var term) t)
        ((variablep term) nil)
        ((fquotep term) nil)
        (t (dumb-occur-var-lst var (fargs term)))))

(defun dumb-occur-var-lst (var lst)
  (cond ((null lst) nil)
        (t (or (dumb-occur-var var (car lst))
               (dumb-occur-var-lst var (cdr lst))))))
)


(defun dumb-occur-in-type-alist (var type-alist)
  (cond
   ((null type-alist)
    nil)
   ((dumb-occur var (caar type-alist))
    t)
   (t
    (dumb-occur-in-type-alist var (cdr type-alist)))))

(defun all-dumb-occur-in-type-alist (vars type-alist)
  (cond
   ((null vars)
    t)
   (t (and (dumb-occur-in-type-alist (car vars) type-alist)
           (all-dumb-occur-in-type-alist (cdr vars) type-alist)))))


(defun dumb-occur-lst-except (term lst lit)

; Like dumb-occur-lst except that it does not look into the first
; element of lst that is equal to lit.  If you think of lst as a
; clause and lit as a literal, we ask whether term occurs in some
; literal of clause other than lit.  In Nqthm we looked for an eq
; occurrence of lit, which we can't do here.  But if there are two
; occurrences of lit in lst, then normally in Nqthm they would not
; be eq and hence we'd look in one of them.  Thus, here we look in
; all the literals of lst after we've seen lit.  This is probably
; unnecessarily complicated.

  (cond ((null lst) nil)
        ((equal lit (car lst))
         (dumb-occur-lst term (cdr lst)))
        (t (or (dumb-occur term (car lst))
               (dumb-occur-lst-except term (cdr lst) lit)))))


(defun logior-lst (lst ans)
  (cond
   ((null lst) ans)
   (t (logior-lst (cdr lst)
                  (logior (car lst) ans)))))

(defun logand-lst (lst ans)
  (cond
   ((null lst) ans)
   (t (logand-lst (cdr lst)
                  (logand (car lst) ans)))))


(defun assoc-equal-cdr (x alist)

; Like assoc-equal but compares against the cdr of each pair in alist.

  (cond ((null alist) nil)
        ((equal x (cdar alist)) (car alist))
        (t (assoc-equal-cdr x (cdr alist)))))

(defun pos-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (posp (car l))
                (pos-listp (cdr l))))))

(defun all-digits-p (lst radix)
  (declare (xargs :guard (and (character-listp lst)
                              (integerp radix)
                              (<= 2 radix)
                              (<= radix 36))))
  (cond ((endp lst) t)
        (t (and (digit-char-p (car lst) radix)
                (all-digits-p (cdr lst) radix)))))

(defun nil-fn ()

; This trivial definition is used for making a sort of placeholder entry,
; *nil-fn-ts-entry*, when simplifying type-alists.  See subst-type-alist1.

  (declare (xargs :guard t :mode :logic))
  nil)

(defun member-char-stringp (chr str i)
  (declare (xargs :guard (and (stringp str)
                              (integerp i)
                              (< i (length str)))
                  :measure (nfix (+ 1 i))))
  (cond ((not (mbt (integerp i)))
         nil)
        ((< i 0) nil)
        (t (or (eql chr (char str i))
               (member-char-stringp chr str (1- i))))))

(defun terminal-substringp1 (str1 str2 max1 max2)
  (declare (xargs :guard (and (stringp str1)
                              (stringp str2)
                              (integerp max1)
                              (integerp max2)
                              (< max1 (length str1))
                              (< max2 (length str2))
                              (<= max1 max2))
                  :measure (nfix (+ 1 max1))))
  (cond ((not (mbt (integerp max1)))
         nil)
        ((< max1 0) t)
        ((eql (char str1 max1) (char str2 max2))
         (terminal-substringp1 str1 str2 (1- max1) (1- max2)))
        (t nil)))

(defun terminal-substringp (str1 str2 max1 max2)
  (declare (xargs :guard (and (stringp str1)
                              (stringp str2)
                              (integerp max1)
                              (integerp max2)
                              (< max1 (length str1))
                              (< max2 (length str2)))))
  (cond ((< max2 max1) nil)
        (t (terminal-substringp1 str1 str2 max1 max2))))

(mutual-recursion

(defun free-varsp (term alist)
  (cond ((variablep term) (not (assoc-eq term alist)))
        ((fquotep term) nil)
        (t (free-varsp-lst (fargs term) alist))))

(defun free-varsp-lst (args alist)
  (cond ((null args) nil)
        (t (or (free-varsp (car args) alist)
               (free-varsp-lst (cdr args) alist)))))

)

(defun merge-car-> (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((> (car (car l1)) (car (car l2)))
         (cons (car l1) (merge-car-> (cdr l1) l2)))
        (t (cons (car l2) (merge-car-> l1 (cdr l2))))))

(defun merge-sort-car-> (l)
  (cond ((null (cdr l)) l)
        (t (merge-car-> (merge-sort-car-> (evens l))
                        (merge-sort-car-> (odds l))))))

(defun merge-car-< (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((< (car (car l1)) (car (car l2)))
         (cons (car l1) (merge-car-< (cdr l1) l2)))
        (t (cons (car l2) (merge-car-< l1 (cdr l2))))))

(defun merge-sort-car-< (l)

; Merge-sort, where elements a and b are compared via (car a) < (car b).

  (cond ((null (cdr l)) l)
        (t (merge-car-< (merge-sort-car-< (evens l))
                        (merge-sort-car-< (odds l))))))

(defun merge-cadr-< (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((< (cadr (car l1)) (cadr (car l2)))
         (cons (car l1) (merge-cadr-< (cdr l1) l2)))
        (t (cons (car l2) (merge-cadr-< l1 (cdr l2))))))

(defun merge-sort-cadr-< (l)

; Merge-sort, where elements a and b are compared via (cadr a) < (cadr b).

  (cond ((null (cdr l)) l)
        (t (merge-cadr-< (merge-sort-cadr-< (evens l))
                         (merge-sort-cadr-< (odds l))))))

(defun clean-up-alist (alist ans)

; Remove duplicate (mod equal) key entries from alist, accumulating the final
; answer onto ans (which is assumed to be nil initially).  We keep the first of
; each duplicate binding and thus we do not change the value of assoc-equal on
; the alist.  However, the order of the pairs in the returned alist is the
; reverse of that in the initial alist.

  (cond ((null alist) ans)
        ((assoc-equal (caar alist) ans)
         (clean-up-alist (cdr alist) ans))
        (t (clean-up-alist (cdr alist) (cons (car alist) ans)))))

(defun duplicate-keysp (alist)

; Determine whether there is a key bound twice (mod equal) in alist.  We return
; the first pair whose key is bound twice, so that we can extract the key from
; that pair in an error report if we like.  (We could return the car of the
; first pair, but if it were nil then we could not distinguish from the error
; case.)

  (cond ((null alist) nil)
        ((assoc-equal (caar alist) (cdr alist))
         (car alist))
        (t (duplicate-keysp (cdr alist)))))

(defun all-variablep (lst)
  (cond ((null lst) t)
        (t (and (variablep (car lst))
                (all-variablep (cdr lst))))))

(defun strip-caddrs (x)
  (declare (xargs :guard (all->=-len x 3)))
  (cond ((null x) nil)
        (t (cons (caddar x) (strip-caddrs (cdr x))))))



; Here is one of the most basic functions in the theorem prover.  It is
; surprising we got so far into the sources without defining it!

; (Students of our code should study this elementary function just to see how
; we recur through terms.  The function instantiates a variable, i.e.,
; (subst-var new old form) substitutes the term new for the variable old in the
; term form.  For example, (subst-var '(car a) 'x '(foo x y)) = '(foo (car a)
; y).)

(mutual-recursion

(defun subst-var (new old form)
  (declare (xargs :guard (and (pseudo-termp new)
                              (variablep old)
                              (pseudo-termp form))))
  (cond ((variablep form)
         (cond ((eq form old) new)
               (t form)))
        ((fquotep form) form)
        (t (cons-term (ffn-symb form)
                      (subst-var-lst new old (fargs form))))))

(defun subst-var-lst (new old l)
  (declare (xargs :guard (and (pseudo-termp new)
                              (variablep old)
                              (pseudo-term-listp l))))
  (cond ((endp l) nil)
        (t (cons (subst-var new old (car l))
                 (subst-var-lst new old (cdr l))))))

)

(defun all-cars-nil (pairs)
  (cond ((endp pairs) t)
        (t (and (null (car (car pairs)))
                (all-cars-nil (cdr pairs))))))

(defun pairwise-subsetp-eq (doms-lst1 doms-lst2)
  (cond ((endp doms-lst1) t)
        ((subsetp-eq (car doms-lst1) (car doms-lst2))
         (pairwise-subsetp-eq (cdr doms-lst1) (cdr doms-lst2)))
        (t nil)))

(defun merge-length (l1 l2)
  (declare (xargs :guard (and (true-list-listp l1)
                              (true-list-listp l2))))
  (cond ((null l1) l2)
        ((null l2) l1)
        ((<= (length (car l1)) (length (car l2)))
         (cons (car l1) (merge-length (cdr l1) l2)))
        (t (cons (car l2) (merge-length l1 (cdr l2))))))

(defun merge-sort-length (l)
  (declare (xargs :guard (true-list-listp l)))
  (cond ((null (cdr l)) l)
        (t (merge-length (merge-sort-length (evens l))
                         (merge-sort-length (odds l))))))

(defun rev-union-equal (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (cond ((endp x) y)
        ((member-equal (car x) y)
         (rev-union-equal (cdr x) y))
        (t
         (rev-union-equal (cdr x) (cons (car x) y)))))



(defun plist-to-alist (lst)

; Convert '(key1 val1 key2 val2 ...) to '((key1 . val1) (key2 . val2) ...).
; In use here, the keys are all in the keyword package.

  (cond ((null lst) nil)
        (t (cons (cons (car lst) (cadr lst))
                 (plist-to-alist (cddr lst))))))

(defun some-cdr-equalp (little big)

; We return t if some cdr of big, including big itself, is equal to little.

  (cond ((equal little big) t)
        ((null big) nil)
        (t (some-cdr-equalp little (cdr big)))))

(defun bounded-length (lst ans max)
  (declare (type (signed-byte 30) ans max))

; We assume ans <= max.

  (the-fixnum
   (cond
    ((null lst) ans)
    ((= ans max) max)
    (t (bounded-length (cdr lst) (+ 1 ans) max)))))

(defun set-difference-assoc-eq (lst alist)
  (declare (xargs :guard (and (true-listp lst)
                              (alistp alist)
                              (or (symbol-listp lst)
                                  (symbol-alistp alist)))))
  (cond ((endp lst) nil)
        ((assoc-eq (car lst) alist)
         (set-difference-assoc-eq (cdr lst) alist))
        (t (cons (car lst) (set-difference-assoc-eq (cdr lst) alist)))))
