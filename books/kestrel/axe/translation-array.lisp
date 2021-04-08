; Renumbering DAG nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")
(include-book "dag-parent-array") ;todo: drop.  but need ALL-DARGP-LESS-THAN-WHEN-NO-ATOMS etc
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;; A translation-array maps each node, up to a given node, to a nodenum,
;; myquotep, or nil (meaning no translation applies for that node).  See also
;; renaming-array.lisp, which disallows nodes being mapped to nil.

;; TODO: Define translation-arrayp and use it instead of translation-arrayp-aux.

;; Checks that, for all indices from top-nodenum-to-check down to 0, the array
;; maps the index to either a quotep, a nodenum, or nil.  Allowing nil makes
;; this different from a renaming-array (TODO: Actually, nil seems to cause an
;; error in translate-args, but see maybe-translate-args).  Since nil is a valid entry in this kind of array,
;; even an empty array satisfies this.
(defund translation-arrayp-aux (top-nodenum-to-check array)
  (declare (xargs :measure (nfix (+ 1 top-nodenum-to-check))
                  :guard (and (array1p 'translation-array array)
                              (integerp top-nodenum-to-check)
                              (< top-nodenum-to-check (alen1 'translation-array array)))))
  (if (not (natp top-nodenum-to-check)) ;optimize?
      t
    (let ((val (aref1 'translation-array array top-nodenum-to-check)))
      (and (or (null val)
               (dargp val))
           (translation-arrayp-aux (+ -1 top-nodenum-to-check) array)))))

(defthm translation-arrayp-aux-of-aset1
  (implies (and (translation-arrayp-aux n translation-array)
                (dargp val)
                (array1p 'translation-array translation-array)
                (< n (alen1 'translation-array translation-array))
                (< index (alen1 'translation-array translation-array))
                (natp index)
                (integerp n))
           (translation-arrayp-aux n (aset1 'translation-array translation-array index val)))
  :hints (("Goal" :expand ()
           :in-theory (e/d (translation-arrayp-aux) (myquotep)))))

(defthm translation-arrayp-aux-of-make-empty-array
  (implies (and (natp len)
                (< n len)
                (natp n)
                (< len 2147483647))
           (translation-arrayp-aux n (make-empty-array 'translation-array len)))
  :hints (("Goal" :expand ((translation-arrayp-aux 0
                                                   (make-empty-array 'translation-array
                                                                     len)
                                                   ))
           :in-theory (enable translation-arrayp-aux))))

;;;
;;; bounded-translation-arrayp-aux
;;;

;; A stronger version of translation-arrayp-aux.
(defund bounded-translation-arrayp-aux (top-nodenum-to-check array bound)
  (declare (xargs :measure (nfix (+ 1 top-nodenum-to-check))
                  :guard (and (array1p 'translation-array array)
                              (integerp top-nodenum-to-check)
                              (< top-nodenum-to-check (alen1 'translation-array array))
                              (natp bound))))
  (if (not (natp top-nodenum-to-check)) ;optimize?
      t
    (let ((val (aref1 'translation-array array top-nodenum-to-check)))
      (and (or (null val)
               (dargp-less-than val bound))
           (bounded-translation-arrayp-aux (+ -1 top-nodenum-to-check) array bound)))))

(defthm bounded-translation-arrayp-aux-when-not-natp
  (implies (not (natp top-nodenum-to-check))
           (bounded-translation-arrayp-aux top-nodenum-to-check array bound))
  :hints (("Goal" :in-theory (enable bounded-translation-arrayp-aux))))

(defthm translation-arrayp-aux-when-bounded-translation-arrayp-aux
  (implies (and (bounded-translation-arrayp-aux top-nodenum-to-check array bound)
                (<= n top-nodenum-to-check)
                (natp n)
                (natp top-nodenum-to-check))
           (translation-arrayp-aux n array))
  :hints (("Goal" :expand ((TRANSLATION-ARRAYP-AUX 0 ARRAY))
           :in-theory (enable bounded-translation-arrayp-aux
                              translation-arrayp-aux))))

(defthm true-listp-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux top-nodenum-to-check translation-array)
                (<= nodenum top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum))
           (equal (true-listp (aref1 'translation-array translation-array nodenum))
                  (or (null (aref1 'translation-array translation-array nodenum))
                      (consp (aref1 'translation-array translation-array nodenum)))))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm integerp-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (equal (integerp (aref1 'translation-array translation-array nodenum))
                  (not (or (null (aref1 'translation-array translation-array nodenum))
                           (consp (aref1 'translation-array translation-array nodenum))))))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm natp-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (equal (natp (aref1 'translation-array translation-array nodenum))
                  (not (or (null (aref1 'translation-array translation-array nodenum))
                           (consp (aref1 'translation-array translation-array nodenum))))))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm cdr-of-aref1-when-translation-arrayp-aux-iff
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (iff (cdr (aref1 'translation-array translation-array nodenum))
                (consp (aref1 'translation-array translation-array nodenum))))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm len-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (equal (len (aref1 'translation-array translation-array nodenum))
                  (if (consp (aref1 'translation-array translation-array nodenum))
                      2
                    0)))
  :hints (("Goal" :expand (translation-arrayp-aux 0 translation-array)
           :in-theory (enable translation-arrayp-aux))))

(defthm acl2-numberp-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (equal (acl2-numberp (aref1 'translation-array translation-array nodenum))
                  (not (or (null (aref1 'translation-array translation-array nodenum))
                           (consp (aref1 'translation-array translation-array nodenum))))))
  :hints (("Goal" :use (:instance natp-of-aref1-when-translation-arrayp-aux)
           :in-theory (disable natp-of-aref1-when-translation-arrayp-aux
                               integerp-of-aref1-when-translation-arrayp-aux))))

(defthm not-<-of-0-and-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (not (< (aref1 'translation-array translation-array nodenum)
                   0)))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm not-<-of-0-and-aref1-when-translation-arrayp-aux-2
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (not (< (aref1 'translation-array translation-array nodenum)
                   -1)))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm <-of--1-and-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (< -1 (aref1 'translation-array translation-array nodenum)))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux))))

(defthm equal-of-nth-0-of-aref1-when-translation-arrayp-aux-and-quote
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (equal (equal 'quote (nth 0 (aref1 'translation-array translation-array nodenum)))
                  (consp (aref1 'translation-array translation-array nodenum))))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux myquotep))))

(defthm quotep-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux nodenum translation-array)
                (natp nodenum))
           (equal (quotep (aref1 'translation-array translation-array nodenum))
                  (consp (aref1 'translation-array translation-array nodenum))))
  :hints (("Goal" :in-theory (enable translation-arrayp-aux myquotep))))

(defthm translation-arrayp-aux-monotone
  (implies (and (translation-arrayp-aux nodenum2 translation-array)
                (<= nodenum nodenum2)
                (natp nodenum2)
                (natp nodenum))
           (translation-arrayp-aux nodenum translation-array))
  :hints (("Goal" :induct (TRANSLATION-ARRAYP-AUX NODENUM2 TRANSLATION-ARRAY)
           :in-theory (enable translation-arrayp-aux))))

(defthm bounded-translation-arrayp-aux-monotone
  (implies (and (bounded-translation-arrayp-aux nodenum2 translation-array bound2)
                (<= nodenum nodenum2)
                (<= bound2 bound)
                (natp nodenum2)
                (natp nodenum))
           (bounded-translation-arrayp-aux nodenum translation-array bound))
  :hints (("Goal" :induct (bounded-translation-arrayp-aux nodenum2 translation-array bound2)
           :in-theory (enable bounded-translation-arrayp-aux))))

(defthm bounded-translation-arrayp-aux-of-make-empty-array
  (implies (and (natp len)
                (< n len)
                (natp n)
                (< len 2147483647))
           (bounded-translation-arrayp-aux n
                                           (make-empty-array 'translation-array
                                                             len)
                                           bound))
  :hints (("Goal" :expand ((bounded-translation-arrayp-aux 0
                                                           (make-empty-array 'translation-array
                                                                             len)
                                                           bound))
           :in-theory (enable bounded-translation-arrayp-aux))))

(defthm <-of-aref1-when-bounded-translation-arrayp-aux
  (implies (and (bounded-translation-arrayp-aux nodenum2 translation-array bound2)
                (<= bound2 bound)
                (<= nodenum nodenum2)
                (natp nodenum)
                (natp nodenum2)
                (aref1 'translation-array translation-array nodenum)
                (not (consp (aref1 'translation-array translation-array nodenum))))
           (< (aref1 'translation-array translation-array nodenum)
              bound))
  :hints (("Goal" :in-theory (enable bounded-translation-arrayp-aux))))

(defthm <-of-aref1-when-bounded-translation-arrayp-aux-special
  (implies (and (bounded-translation-arrayp-aux nodenum translation-array bound)
                (natp nodenum)
                (aref1 'translation-array translation-array nodenum)
                (not (consp (aref1 'translation-array translation-array nodenum))))
           (< (aref1 'translation-array translation-array nodenum)
              bound))
  :hints (("Goal" :in-theory (enable bounded-translation-arrayp-aux))))

;;;
;;; translate-args
;;;

;; Translates all the ARGS according to the TRANSLATION-ARRAY.  Throws an error
;; if any of them doesn't translate to anything.
;; TODO: Consider using cons-with-hint here.
(defund translate-args (args translation-array)
  (declare (xargs :guard (and (true-listp args)
                              (array1p 'translation-array translation-array)
                              (all-dargp-less-than args (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))
                  :guard-hints (("Goal" :in-theory (enable))) ;todo: make a fw-chaining rule for the dims
                  ))
  (if (endp args)
      nil
    (let ((arg (first args)))
      (if (consp arg) ;test for quotep
          (cons arg (translate-args (rest args) translation-array))
        (let ((res (aref1 'translation-array translation-array arg)))
          (if (not res) ;; TODO: Drop this check (translation array should map all child nodes)
              (er hard? 'translate-args "Node ~x0 did not translate to anything." arg)
            (cons res (translate-args (rest args) translation-array))))))))

(defthm bounded-translation-arrayp-aux-of-aset1
  (implies (and (bounded-translation-arrayp-aux n translation-array bound)
                (dargp-less-than val bound)
                (array1p 'translation-array translation-array)
                (< n (alen1 'translation-array translation-array))
                (< index (alen1 'translation-array translation-array))
                (natp index)
                (integerp n))
           (bounded-translation-arrayp-aux n (aset1 'translation-array translation-array index val) bound))
  :hints (("Goal" :in-theory (e/d (bounded-translation-arrayp-aux) (myquotep)))))

(defthm dargp-less-than-of-aref1-when-bounded-translation-arrayp-aux
  (implies (and (bounded-translation-arrayp-aux n translation-array bound)
                (aref1 'translation-array translation-array n)
                (natp n))
           (dargp-less-than (aref1 'translation-array translation-array n)
                                       bound))
  :hints (("Goal" :in-theory (e/d (bounded-translation-arrayp-aux) (DARGP-LESS-THAN)))))

(defthm dargp-of-aref1-when-translation-arrayp-aux
  (implies (and (translation-arrayp-aux n translation-array)
                (aref1 'translation-array translation-array n)
                (natp n))
           (dargp (aref1 'translation-array translation-array n)))
  :hints (("Goal" :in-theory (e/d (translation-arrayp-aux) (DARGP)))))

(defthm not-<-of-+-of--1-and-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (natp n)
                (< n (len args))
                (not (consp (nth n args)))
;                (all-integerp args)
                (integerp bound))
           (not (< (+ -1 bound)
                   (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than (:i nth)) ()))))

;dup
(defthmd not-<-of-one-less-and-nth
  (implies (and (all-< items bound)
                (all-natp items)
                (natp bound)
                (natp n)
                (< n (len items)))
           (not (< (binary-+ '-1 bound) (nth n items))))
  :hints (("Goal" :in-theory (e/d (all-< nth) (nth-of-cdr)))))
(local (in-theory (enable not-<-of-one-less-and-nth)))

(defthm all-dargp-less-than-of-translate-args
  (implies (and (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound)
                (all-dargp-less-than args (alen1 'translation-array translation-array))
                (array1p 'translation-array translation-array))
           (all-dargp-less-than (translate-args args translation-array) bound))
  :hints (("Goal" :in-theory (e/d (translate-args CAR-BECOMES-NTH-OF-0)
                                  (dargp-less-than)))))

(defthm all-dargp-of-translate-args
  (implies (and (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-dargp-less-than args (alen1 'translation-array translation-array))
                (array1p 'translation-array translation-array))
           (all-dargp (translate-args args translation-array)))
  :hints (("Goal" :in-theory (e/d (translate-args) (dargp)))))


(defthm <=-of-aref1-when-bounded-translation-arrayp-aux-special
  (implies (and (bounded-translation-arrayp-aux nodenum translation-array (+ 1 bound))
                (natp nodenum)
                (aref1 'translation-array translation-array nodenum)
                (not (consp (aref1 'translation-array translation-array nodenum)))
                (natp bound))
           (<= (aref1 'translation-array translation-array nodenum)
               bound))
  :hints (("Goal" :use (:instance <-of-aref1-when-bounded-translation-arrayp-aux-special
                                  (bound (+ 1 bound)))
           :in-theory (disable <-of-aref1-when-bounded-translation-arrayp-aux-special
                               <-of-aref1-when-bounded-translation-arrayp-aux))))

;;;
;;; translate-args-with-changep
;;;

;; TODO: Use this more
;; Returns (mv erp new-args changep).
;; TODO: Strengthen guard and get rid of the error check and the erp return value.
;; We could use cons-with-hint here instead of passing around changep, but the caller looks at changep.
(defund translate-args-with-changep (args translation-array)
  (declare (xargs :guard (and (true-listp args)
                              (array1p 'translation-array translation-array)
                              (all-dargp-less-than args (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))))
  (if (endp args)
      (mv (erp-nil) nil nil)
    (b* (((mv erp new-rest-args rest-changep)
          (translate-args-with-changep (rest args) translation-array))
         ((when erp) (mv erp args nil))
         ((mv erp new-first-arg first-changep) ;todo: drop erp
          (let ((first-arg (first args)))
            (if (consp first-arg) ;test for a quotep, which translates to itself
                (mv (erp-nil) first-arg nil)
              ;; first-arg is a nodenum:
              (let ((new-first-arg (aref1 'translation-array translation-array first-arg)))
                (if (not new-first-arg) ;; TODO: Drop this check (translation array should map all child nodes)
                    (prog2$ (er hard? 'translate-args "Node did not translate to anything.")
                            (mv (erp-t) nil nil))
                  (mv (erp-nil) new-first-arg (not (equal new-first-arg first-arg)))))))) ;could use = if we know that consps can't occur
         ((when erp) (mv erp args nil))
         (changep (or first-changep rest-changep)))
      (mv (erp-nil)
          (if changep
              (cons new-first-arg new-rest-args)
            ;; Avoid reconsing if no change:
            args)
          changep))))

(defthm mv-nth-1-of-translate-args-with-changep-when-no-change
  (implies (and (not (mv-nth 0 (translate-args-with-changep args translation-array))) ; no error
                (not (mv-nth 2 (translate-args-with-changep args translation-array))) ;no change
                (true-listp args))
           (equal (mv-nth 1 (translate-args-with-changep args translation-array))
                  args))
  :hints (("Goal" :in-theory (enable translate-args-with-changep))))

;move
(defthm all-dargp-less-than-when-all-dargp-less-than-of-cdr-cheap
  (implies (all-dargp-less-than (cdr items) bound)
           (equal (all-dargp-less-than items bound)
                  (if (not (consp items))
                      t
                    (dargp-less-than (car items) bound))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

(defthm all-dargp-of-mv-nth-1-of-translate-args-with-changep
  (implies (and (not (mv-nth 0 (translate-args-with-changep args translation-array)))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-dargp-less-than args (alen1 'translation-array translation-array))
                (array1p 'translation-array translation-array))
           (all-dargp (mv-nth 1 (translate-args-with-changep args translation-array))))
  :hints (("Goal" :in-theory (e/d (translate-args-with-changep car-becomes-nth-of-0) (dargp)))))

(defthm true-listp-mv-nth-1-of-translate-args-with-changep
  (implies (true-listp args)
           (true-listp (mv-nth 1 (translate-args-with-changep args translation-array))))
  :hints (("Goal" :in-theory (e/d (translate-args-with-changep car-becomes-nth-of-0) (dargp)))))

(defthm all-dargp-less-than-of-mv-nth-1-of-translate-args-with-changep
  (implies (and (not (mv-nth 0 (translate-args-with-changep args translation-array)))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound)
                (all-dargp-less-than args (alen1 'translation-array translation-array))
                (array1p 'translation-array translation-array)
                (true-listp args))
           (all-dargp-less-than (mv-nth 1 (translate-args-with-changep args translation-array)) bound))
  :hints (("SubGoal *1/8" :do-not '(generalize eliminate-destructors)
           :cases ((consp (NTH 0 ARGS)))
           :use (:instance DARGP-LESS-THAN-OF-AREF1-WHEN-BOUNDED-TRANSLATION-ARRAYP-AUX
                           (n (NTH 0 ARGS)))
           :in-theory (e/d (translate-args-with-changep car-becomes-nth-of-0
                                                        all-dargp-less-than)
                           (dargp-less-than-of-aref1-when-bounded-translation-arrayp-aux
                            dargp)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (translate-args-with-changep car-becomes-nth-of-0)
                           (dargp)))))


;;;
;;; maybe-translate-args
;;;

;; This version allows an arg to not translate to anything (meaning that it is unchanged).
(defund maybe-translate-args (args translation-array)
  (declare (xargs :guard (and (true-listp args)
                              (array1p 'translation-array translation-array)
                              (all-dargp-less-than args (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))
                  :guard-hints (("Goal" :in-theory (enable))) ;todo: make a fw-chaining rule for the dims
                  ))
  (if (endp args)
      nil
    (let ((arg (first args)))
      (if (consp arg) ;test for quotep
          (cons-with-hint arg (maybe-translate-args (rest args) translation-array) args)
        ;; it's a nodenum, so see if it is translated:
        (let ((res (aref1 'translation-array translation-array arg)))
          (if res
              ;; arg gets translated to res:
              (cons res (maybe-translate-args (rest args) translation-array))
            ;; no change to arg:
            (cons-with-hint arg (maybe-translate-args (rest args) translation-array) args)))))))

(defthm all-dargp-less-than-of-maybe-translate-args
  (implies (and (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound)
                (all-dargp-less-than args (alen1 'translation-array translation-array))
                (all-dargp-less-than args bound)
                (array1p 'translation-array translation-array))
           (all-dargp-less-than (maybe-translate-args args translation-array) bound))
  :hints (("Goal" :in-theory (e/d (maybe-translate-args CAR-BECOMES-NTH-OF-0
                                                        EQUAL-OF-QUOTE-AND-NTH-0-OF-NTH-WHEN-ALL-DARGP)
                                  (dargp-less-than)))))

(defthm all-dargp-of-maybe-translate-args
  (implies (and (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-dargp-less-than args (alen1 'translation-array translation-array))
                (array1p 'translation-array translation-array))
           (all-dargp (maybe-translate-args args translation-array)))
  :hints (("Goal" :in-theory (e/d (maybe-translate-args) (dargp)))))
