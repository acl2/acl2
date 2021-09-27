; Populating the assumption-array
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assumption-array")
(include-book "dag-arrays")
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))

(local (in-theory (disable symbol-listp)))

(local
 (defthm nat-listp-of-reverse-list
   (implies (NAT-LISTP x)
            (NAT-LISTP (REVERSE-LIST x)))
   :hints (("Goal" :in-theory (enable NAT-LISTP)))))

;; Returns (mv assumption-nodenum assumption-item), where the ASSUMPTION-ITEM
;; is a dargp or :non-nil suitable for storing in the assumption-array for
;; ASSUMPTION-NODENUM.  Note that the assertion may not be about
;; LITERAL-NODENUM itself but rather about one of its children.
(defund assumption-array-info-for-literal (literal-nodenum dag-array dag-len known-booleans print)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp literal-nodenum)
                              (< literal-nodenum dag-len)
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0
                                                         natp-of-+-of-1
                                                         <-of-+-of-1-strengthen-2
                                                         consp-when-true-listp-and-non-nil)
                                                        (natp)))))
           (ignore dag-len) ;only used in the guard
           )
  (let ((expr-to-assume-false (aref1 'dag-array dag-array literal-nodenum)))
    (if (not (and (call-of 'not expr-to-assume-false)
                  (consp (dargs expr-to-assume-false)) ; for guard proof
                  (atom (darg1 expr-to-assume-false)) ;makes sure it's a nodenum
                  ))
        ;; the expr-to-assume-false is something other than a call of NOT, so
        ;; we just indicate a replacement of it by NIL:
        (mv literal-nodenum *nil*)
      ;; EXPR-TO-ASSUME-FALSE is of the form (not <nodenum-to-assume-non-nil>):
      (let* ((nodenum-to-assume-non-nil (darg1 expr-to-assume-false))
             (expr-to-assume-non-nil (aref1 'dag-array dag-array nodenum-to-assume-non-nil)))
        (if (and (call-of 'equal expr-to-assume-non-nil)
                 (consp (rest (dargs expr-to-assume-non-nil))))
            ;; The expr-to-assume-non-nil is a call of equal:
            (let ((equated-thing1 (darg1 expr-to-assume-non-nil))
                  (equated-thing2 (darg2 expr-to-assume-non-nil)))
              (if (and (atom equated-thing1)  ;check for a nodenum
                       (consp equated-thing2) ;check for a quotep
                       )
                  ;; The expr-to-assume-non-nil is of the form (equal <nodenum> <constant>), so we add the constant as a
                  ;; replacement for the nodenum:
                  (mv equated-thing1 equated-thing2)
                (if (and (consp equated-thing1) ;check for a quotep
                         (atom equated-thing2)  ;check for a nodenum
                         )
                    ;; The expr-to-assume-non-nil is of the form (equal <constant> <nodenum>), so we add the constant as a
                    ;; replacement for the nodenum:
                    (mv equated-thing2 equated-thing1)
                  ;; The expr-to-assume-non-nil is an equality but not one that
                  ;; gets special handling, so we record the fact that the
                  ;; entire equality is t.  TODO: Consider reordering the
                  ;; equality?
                  (mv nodenum-to-assume-non-nil *t*))))
          ;; The expr-to-assume-non-nil is not a call of equal, so we check
          ;; whether it is a call of a known boolean: TODO: I suppose we might
          ;; have an assumption that the node is boolean and want to use that
          ;; information here.
          (if (and (consp expr-to-assume-non-nil)
                   (member-eq (ffn-symb expr-to-assume-non-nil) known-booleans))
              ;; We are assuming a boolean thing to be non-nil, so we can replace it with t:
              (mv nodenum-to-assume-non-nil *t*)
            ;; All we know is that the thing is non-nil:
            (progn$ (and print
                         (if (consp expr-to-assume-non-nil)
                             (cw "NOTE: Non-known-boolean assumption (call of ~x0) found.~%" (ffn-symb expr-to-assume-non-nil))
                           (cw "NOTE: Variable assumption, ~x0, found (not a known boolean).~%" expr-to-assume-non-nil)))
                    (mv nodenum-to-assume-non-nil :non-nil))))))))

(defthm natp-of-mv-nth-0-of-assumption-array-info-for-literal
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp literal-nodenum)
                (< literal-nodenum dag-len))
           (natp (mv-nth 0 (assumption-array-info-for-literal literal-nodenum dag-array dag-len known-booleans print))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (assumption-array-info-for-literal
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm <=-of-0-and-mv-nth-0-of-assumption-array-info-for-literal
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp literal-nodenum)
                (< literal-nodenum dag-len))
           (<= 0 (mv-nth 0 (assumption-array-info-for-literal literal-nodenum dag-array dag-len known-booleans print))))
  :hints (("Goal" :use natp-of-mv-nth-0-of-assumption-array-info-for-literal
           :in-theory (disable natp-of-mv-nth-0-of-assumption-array-info-for-literal))))

(defthm integerp-of-mv-nth-0-of-assumption-array-info-for-literal
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp literal-nodenum)
                (< literal-nodenum dag-len))
           (integerp (mv-nth 0 (assumption-array-info-for-literal literal-nodenum dag-array dag-len known-booleans print))))
  :hints (("Goal" :use natp-of-mv-nth-0-of-assumption-array-info-for-literal
           :in-theory (disable natp-of-mv-nth-0-of-assumption-array-info-for-literal))))

(defthm <=-of-mv-nth-0-of-assumption-array-info-for-literal
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp literal-nodenum)
                (< literal-nodenum dag-len))
           (<= (mv-nth 0 (assumption-array-info-for-literal literal-nodenum dag-array dag-len known-booleans print))
               literal-nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
           :in-theory (e/d (assumption-array-info-for-literal
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (natp)))))

(defthm <-of-mv-nth-0-of-assumption-array-info-for-literal-gen
  (implies (and (<= (+ 1 literal-nodenum) bound)
                ;(natp bound)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp literal-nodenum)
                (< literal-nodenum dag-len))
           (< (mv-nth 0 (assumption-array-info-for-literal literal-nodenum dag-array dag-len known-booleans print))
              bound))
  :hints (("Goal" :use (<=-of-mv-nth-0-of-assumption-array-info-for-literal)
           :in-theory (disable <=-of-mv-nth-0-of-assumption-array-info-for-literal))))

;; We always add some info (about some node) for a literal
(defthm assumption-itemp-of-mv-nth-1-of-assumption-array-info-for-literal
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp literal-nodenum)
                (< literal-nodenum dag-len))
           (assumption-itemp (mv-nth 1 (assumption-array-info-for-literal literal-nodenum dag-array dag-len known-booleans print))))
  :hints (("Goal" ; :use (:instance TYPE-OF-AREF1-WHEN-ASSUMPTION-ARRAYP)
           :in-theory (e/d (assumption-array-info-for-literal car-becomes-nth-of-0)
                           (TYPE-OF-AREF1-WHEN-ASSUMPTION-ARRAYP
                            quotep)))))

(local
 (defthm not-of-nth-1-when-myquotep
   (implies (myquotep x)
            (iff (nth 1 x)
                 (not (equal x *nil*))))))

(local
 (defthm nth-0-when-myquotep
   (implies (myquotep x)
            (equal (nth 0 x)
                   'quote))))

;; (local
;;  (defthmd myquotep-when-assumption-itemp
;;    (implies (assumption-itemp item)
;;             (equal (myquotep item)
;;                    (not (equal item :non-nil))))
;;    :hints (("Goal" :in-theory (enable assumption-itemp)))))

(local
 (defthm equal-of-non-nil-when-assumption-itemp
   (implies (assumption-itemp item)
            (equal (equal item :non-nil)
                   (not (myquotep item))))
   :hints (("Goal" :in-theory (enable assumption-itemp)))))

(in-theory (disable assumption-itemp))

;; Returns (mv provedp literals assumption-array redundancy-presentp).  Walk
;; through the NODENUMS-TO_ASSUME false, populating the ASSUMPTION-ARRAY with
;; information from them.  This can prove the clause if a contradiction is
;; discovered, and it can drop literals with redundant information.  Tricky
;; case: If an earlier literal told us a nodenum was :non-nil but the current
;; literal tells us it is a particular non-nil constant: We would like to have
;; dropped the earlier literal, but it is too late.  So we store the constant
;; but set the redundancy-presentp flag to indicate that we need to make a
;; second pass to drop weaker literals whose information is implied by the
;; assumption-array.  The reason we don't want reundnant literals is that when
;; rewriting a literal we clear its assumption info in the array, which would
;; present us from detecting contradictions and redundant info at that point.
(defund make-assumption-array-aux (literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp literals)
                              (all-< literals dag-len)
                              (true-listp kept-literals-acc)
                              (assumption-arrayp 'assumption-array assumption-array)
                              (equal (alen1 'assumption-array assumption-array)
                                     dag-len)
                              (booleanp redundancy-presentp)
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :use ((:instance natp-of-mv-nth-0-of-assumption-array-info-for-literal
                                                         (literal-nodenum (NTH 0 LITERALS))
                                                         (dag-len (ALEN1 'ASSUMPTION-ARRAY
                                                                         ASSUMPTION-ARRAY)))
                                              (:instance assumption-itemp-of-mv-nth-1-of-assumption-array-info-for-literal
                                                         (literal-nodenum (NTH 0 LITERALS))
                                                         (dag-len (ALEN1 'ASSUMPTION-ARRAY
                                                                         ASSUMPTION-ARRAY)))
                                              (:instance type-of-aref1-when-assumption-arrayp
                                                         (array-name 'assumption-array)
                                                         (array assumption-array)
                                                         (index (MV-NTH 0
                                                                        (ASSUMPTION-ARRAY-INFO-FOR-LITERAL (NTH 0 LITERALS)
                                                                                                           DAG-ARRAY
                                                                                                           (ALEN1 'ASSUMPTION-ARRAY
                                                                                                                  ASSUMPTION-ARRAY)
                                                                                                           KNOWN-BOOLEANS print)))))
                                 :in-theory (e/d (car-becomes-nth-of-0
                                                  natp-of-+-of-1
                                                  <-of-+-of-1-strengthen-2
                                                  consp-when-true-listp-and-non-nil)
                                                 (assumption-itemp
                                                  MYQUOTEP
                                                  natp
                                                  assumption-itemp-of-mv-nth-1-of-assumption-array-info-for-literal
                                                  natp-of-mv-nth-0-of-assumption-array-info-for-literal
                                                  type-of-aref1-when-assumption-arrayp))))))
  (if (endp literals)
      (mv nil                         ; didn't prove the whole clause
          (reverse kept-literals-acc) ; todo: consider not reversing
          assumption-array
          redundancy-presentp)
    (b* ((literal (first literals))
         ;; Get the nodenum and assumption-item which together represent the information in this literal:
         ((mv assumption-nodenum assumption-item)
          (assumption-array-info-for-literal literal dag-array dag-len known-booleans print))
         ;; Get the existing inforation for assumption-nodenum in the assumption-array, if any:
         (existing-assumption-item (aref1 'assumption-array assumption-array assumption-nodenum)))
      (if (not existing-assumption-item)
          ;; No existing info to check for contradictions or redundancy:
          (make-assumption-array-aux (rest literals)
                                     (cons literal kept-literals-acc) ; keep this literal
                                     ;; Record the information from this literal:
                                     (aset1 'assumption-array assumption-array assumption-nodenum assumption-item)
                                     redundancy-presentp ;no new redundancy
                                     dag-array dag-len known-booleans print)
        ;; There is an existing entry for assumption-nodenum, so we have to
        ;; consider some cases.
        (if (eq :non-nil existing-assumption-item)
            ;; We already know the assumption-nodenum is non-nil:
            (if (eq :non-nil assumption-item)
                ;; This literal tells us something we already know, so drop it:
                (progn$ (cw "NOTE: Dropping redundant literal.~%")
                        (make-assumption-array-aux (rest literals)
                                                   kept-literals-acc ; literal not added
                                                   assumption-array ; no new info to store
                                                   redundancy-presentp ;no new redundancy
                                                   dag-array dag-len known-booleans print))
              (if (and (mbt (myquotep assumption-item)) ;just to check
                       (unquote assumption-item))
                  ;; We already know it is :non-nil, and now we know which
                  ;; non-nil constant it is. This is the "tricky case"; see
                  ;; comment above.
                  (make-assumption-array-aux (rest literals)
                                             (cons literal kept-literals-acc) ; keep this literal since it is stronger
                                             ;; Replace the :non-nil from before with the constant from this literal:
                                             (aset1 'assumption-array assumption-array assumption-nodenum assumption-item)
                                             t ;; redundancy is present (the earlier literal that told us merely :non-nil)
                                             dag-array dag-len known-booleans print)
                (if (mbt (equal *nil* assumption-item)) ;we know this is true
                    ;; This literal gives us a contradiction
                    (prog2$ (cw "NOTE: Contradiction found among literals.~%") ;todo: print it?
                            (mv t ;proved the entire clause
                                nil assumption-array redundancy-presentp))
                  ;; Can never happen:
                  (prog2$ (er hard 'make-assumption-array-aux "Bad assumption-item: ~x0." assumption-item)
                          (mv nil nil nil nil)))))
          (if (equal *nil* existing-assumption-item)
              ;; We already know the assumption-nodenum is nil:
              (if (equal *nil* assumption-item)
                  ;; This literal tells us something we already know, so drop it:
                  (progn$ (and print (cw "NOTE: Dropping redundant literal.~%"))
                          (make-assumption-array-aux (rest literals)
                                                     kept-literals-acc ; literal not added
                                                     assumption-array ; no new info to store
                                                     redundancy-presentp ; no new redundancy
                                                     dag-array dag-len known-booleans print))
                ;; Otherwise, the assumption-item must be either :non-nil or some
                ;; non-nil constant, but we check here just to be sure:
                (if (mbt (or (eq :non-nil assumption-item)
                             (and (myquotep assumption-item)
                                  (bool-fix (unquote assumption-item)))))
                    ;; This literal gives us a contradiction
                    (prog2$ (and print (cw "NOTE: Contradiction found among literals.~%")) ;todo: print it?
                            (mv t ;proved the entire clause
                                nil assumption-array redundancy-presentp))
                  ;; Can never happen:
                  (prog2$ (er hard 'make-assumption-array-aux "Bad assumption-item: ~x0." assumption-item)
                          (mv nil nil nil nil))))
            (if (mbt (and (myquotep existing-assumption-item)
                          (bool-fix (unquote existing-assumption-item))))
                ;; We already know the assumption-nodenum is some particular non-nil constant:
                (if (eq :non-nil assumption-item)
                    ;; This literal tells us something we already know, so drop it:
                    (progn$ (and print (cw "NOTE: Dropping redundant literal.~%"))
                            (make-assumption-array-aux (rest literals)
                                                       kept-literals-acc ; literal not added
                                                       assumption-array ; no new info to store
                                                       redundancy-presentp ; no new redundancy
                                                       dag-array dag-len known-booleans print))
                  (if (mbt (myquotep assumption-item)) ; just to check
                      ;; They are both quoteps:
                      (if (not (equal (unquote existing-assumption-item)
                                      (unquote assumption-item)))
                          ;; This literal gives us a contradiction (the node can't be two differerent constants):
                          (prog2$ (and print (cw "NOTE: Contradiction found among literals.~%")) ;todo: print it?
                                  (mv t ;proved the entire clause
                                      nil assumption-array redundancy-presentp))
                        ;; This literal tells us something we already know, so drop it:
                        (progn$ (and print (cw "NOTE: Dropping redundant literal.~%"))
                                (make-assumption-array-aux (rest literals)
                                                           kept-literals-acc ; literal not added
                                                           assumption-array ; no new info to store
                                                           redundancy-presentp ; no new redundancy
                                                           dag-array dag-len known-booleans print)))
                    ;; Can never happen:
                    (prog2$ (er hard 'make-assumption-array-aux "Bad assumption-item: ~x0." assumption-item)
                            (mv nil nil nil nil))))
              ;; Can never happen:
              (prog2$ (er hard 'make-assumption-array-aux "Bad assumption-item: ~x0." assumption-item)
                      (mv nil nil nil nil)))))))))

(defthm booleanp-of-mv-nth-0-of-make-assumption-array-aux
  (booleanp (mv-nth 0 (make-assumption-array-aux literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print)))
  :hints (("Goal"
           :in-theory (e/d (make-assumption-array-aux
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (quotep
                            myquotep
                            natp)))))

(defthm true-listp-of-mv-nth-1-of-make-assumption-array-aux
  (implies (true-listp kept-literals-acc)
           (true-listp (mv-nth 1 (make-assumption-array-aux literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print))))
  :hints (("Goal"
           :in-theory (e/d (make-assumption-array-aux
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (quotep
                            myquotep
                            natp)))))

(defthm assumption-arrayp-of-mv-nth-2-of-make-assumption-array-aux
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literals)
                (all-< literals dag-len)
                ;(true-listp kept-literals-acc)
                (assumption-arrayp 'assumption-array assumption-array)
                (equal (alen1 'assumption-array assumption-array)
                       dag-len)
                (booleanp redundancy-presentp))
           (assumption-arrayp 'assumption-array (mv-nth 2 (make-assumption-array-aux literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print))))
  :hints (("Goal"
           :in-theory (e/d (make-assumption-array-aux
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (quotep
                            myquotep
                            natp)))))

(defthm alen1-of-mv-nth-2-of-make-assumption-array-aux
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literals)
                (all-< literals dag-len)
                ;(true-listp kept-literals-acc)
                (assumption-arrayp 'assumption-array assumption-array)
                (equal (alen1 'assumption-array assumption-array)
                       dag-len)
                (booleanp redundancy-presentp))
           (equal (alen1 'assumption-array (mv-nth 2 (make-assumption-array-aux literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print)))
                  (alen1 'assumption-array assumption-array)
                  ))
  :hints (("Goal"
           :in-theory (e/d (make-assumption-array-aux
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (quotep
                            MYQUOTEP
                            natp)))))

(defthm nat-listp-of-mv-nth-1-of-make-assumption-array-aux
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literals)
                (all-< literals dag-len)
                (nat-listp kept-literals-acc)
                (assumption-arrayp 'assumption-array assumption-array)
                (equal (alen1 'assumption-array assumption-array)
                       dag-len)
                (booleanp redundancy-presentp))
           (nat-listp (mv-nth 1 (make-assumption-array-aux literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print))))
  :hints (("Goal"
           :in-theory (e/d (make-assumption-array-aux
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (quotep
                            MYQUOTEP
                            natp)))))

(defthm all-<-of-mv-nth-1-of-make-assumption-array-aux
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literals)
                (all-< literals dag-len)
                (nat-listp kept-literals-acc)
                (all-< kept-literals-acc dag-len)
                (assumption-arrayp 'assumption-array assumption-array)
                (equal (alen1 'assumption-array assumption-array)
                       dag-len)
                (booleanp redundancy-presentp))
           (all-< (mv-nth 1 (make-assumption-array-aux literals kept-literals-acc assumption-array redundancy-presentp dag-array dag-len known-booleans print))
                  dag-len))
  :hints (("Goal"
           :in-theory (e/d (make-assumption-array-aux
                            car-becomes-nth-of-0
                            natp-of-+-of-1
                            <-of-+-of-1-strengthen-2
                            consp-when-true-listp-and-non-nil)
                           (quotep
                            MYQUOTEP
                            natp)))))

;; Drop literals that tell us a node is :non-nil when the array tells us the node is some particular non-nil constant
(defund drop-redundant-literals (literals kept-literals-acc assumption-array dag-array dag-len known-booleans print)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp literals)
                              (all-< literals dag-len)
                              (nat-listp kept-literals-acc)
                              (all-< kept-literals-acc dag-len)
                              (assumption-arrayp 'assumption-array assumption-array)
                              (equal (alen1 'assumption-array assumption-array)
                                     dag-len)
                              (symbol-listp known-booleans))))
  (if (endp literals)
      (reverse kept-literals-acc)
    (b* ((literal (first literals))
         ;; Get the nodenum and assumption-item which together represent the information in this literal:
         ((mv assumption-nodenum assumption-item)
          (assumption-array-info-for-literal literal dag-array dag-len known-booleans print))
         ;; Get the existing inforation for assumption-nodenum in the assumption-array (probably some such info will always exist):
         (existing-assumption-item (aref1 'assumption-array assumption-array assumption-nodenum)))
      (if (and (eq :non-nil assumption-item)
               ;; existing-assumption-item is some non-nil constant:
               (myquotep existing-assumption-item) ;optimize?
               (unquote existing-assumption-item))
          (progn$ (cw "NOTE: Dropping redundant literal.~%")
                  (drop-redundant-literals (rest literals)
                                           kept-literals-acc ; drop the literal
                                           assumption-array dag-array dag-len known-booleans print))
        (drop-redundant-literals (rest literals)
                                 (cons literal kept-literals-acc) ; keep the literal
                                 assumption-array dag-array dag-len known-booleans print)))))

(defthm drop-redundant-literals-return-type
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literals)
                (all-< literals dag-len)
                (nat-listp kept-literals-acc)
                (all-< kept-literals-acc dag-len)
                (assumption-arrayp 'assumption-array assumption-array)
                (equal (alen1 'assumption-array assumption-array)
                       dag-len))
           (and (nat-listp (drop-redundant-literals literals kept-literals-acc assumption-array dag-array dag-len known-booleans print))
                (all-< (drop-redundant-literals literals kept-literals-acc assumption-array dag-array dag-len known-booleans print)
                       dag-len)))
  :hints (("Goal" :in-theory (enable drop-redundant-literals))))

(defthm true-listp-of-drop-redundant-literals
  (implies (true-listp kept-literals-acc)
           (true-listp (drop-redundant-literals literals kept-literals-acc assumption-array dag-array dag-len known-booleans print)))
   :hints (("Goal" :in-theory (enable drop-redundant-literals))))

;; Returns (mv provedp literals assumption-array).
;; Creates an assumption-array containing the information from the
;; literals.
(defund make-assumption-array (literals dag-array dag-len known-booleans print)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (posp dag-len) ;can't make an empty assumptions array
                              (nat-listp literals)
                              (all-< literals dag-len)
                              (symbol-listp known-booleans))))
  (b* ((assumption-array (make-empty-array 'assumption-array dag-len))
       ((mv provedp literals assumption-array redundancy-presentp)
        (make-assumption-array-aux literals nil assumption-array nil dag-array dag-len known-booleans print))
       ((when provedp)
        (mv provedp nil assumption-array)))
    (if redundancy-presentp
        ;; Need a second pass to drop literals that give us :non-nil for a node which another literal gives of *t* for:
        (mv nil ; did not prove the whole clause
            (drop-redundant-literals literals nil assumption-array dag-array dag-len known-booleans print)
            assumption-array)
      (mv nil ; did not prove the whole clause
          literals
          assumption-array))))

(defthm make-assumption-array-return-type
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (consp literals) ;(posp dag-len) ;can't make an empty assumptions array
                (nat-listp literals)
                (all-< literals dag-len))
           (mv-let (provedp literals assumption-array)
             (make-assumption-array literals dag-array dag-len known-booleans print)
             (and (booleanp provedp)
                  (nat-listp literals)
                  (all-< literals dag-len)
                  (assumption-arrayp 'assumption-array assumption-array))))
  :hints (("Goal" :cases ((equal 0 dag-len))
           :in-theory (enable make-assumption-array))))

(defthm make-assumption-array-return-type-2
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (consp literals) ;(posp dag-len) ;can't make an empty assumptions array
                (nat-listp literals)
                (all-< literals dag-len))
           (mv-let (provedp literals assumption-array)
             (make-assumption-array literals dag-array dag-len known-booleans print)
             (declare (ignore provedp literals))
             (equal (alen1 'assumption-array assumption-array)
                    dag-len)))
  :hints (("Goal" :cases ((equal 0 dag-len))
           :in-theory (enable make-assumption-array))))

(defthm make-assumption-array-return-type-3
  (mv-let (provedp literals assumption-array)
    (make-assumption-array literals dag-array dag-len known-booleans print)
    (declare (ignore provedp assumption-array))
    (true-listp literals))
  :hints (("Goal" :cases ((equal 0 dag-len))
           :in-theory (enable make-assumption-array))))
