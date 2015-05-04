; array1.lisp -- a book about one-dimensional arrays
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bishop Brock
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

; Note: This book was originally developed in a version of ACL2 where guards
; were part of the logic. It is technically possible to weaken the hypotheses
; of many of the lemmas, but time has not permitted us to do this.

; Modified by Jared Davis, September 2014, to port documentation to xdoc.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc array1
  :parents (data-structures)
  :short "A book of lemmas that characterize 1-dimensional arrays."
  :long "<p>Because many of the functions characterized by this book are
non-recursive, one should always @(see DISABLE) the theory
@('ARRAY1-FUNCTIONS') after including this book, or the lemmas will not be
applicable.</p>

<p>The lemmas exported by this book should completely characterize
1-dimensional arrays for most purposes.  Given the lemmas exported by this
book, it should not be necessary to @(see ENABLE) any of the 1-dimensional
array functions except under special circumstances.</p>

<p>This book defines a function @(see RESET-ARRAY1) that clears an array,
effectively resetting each element of the array to the default value.  This
book also includes a macro, @(see DEFARRAY1TYPE), which defines recognizers and
supporting lemmas for 1-dimensional arrays whose elements are all of a fixed
type.</p>")


;;;****************************************************************************
;;;
;;;    These are general lemmas about ALISTs and ALIST functions.  None of
;;;    these lemmas are exported by this book.  Perhaps someday they will
;;;    appear in an ALIST book.
;;;
;;;****************************************************************************

(local (defthm eqlable-alistp-implies-alistp
         (implies (eqlable-alistp l)
                  (alistp l))
         :rule-classes (:rewrite :forward-chaining)))

(local (defthm assoc-properties
         (implies (and (eqlable-alistp l)
                       (assoc x l))
                  (and (consp (assoc x l))
                       (equal (car (assoc x l)) x)))))

(local (defthm eqlablep-car-assoc
         (implies (and (eqlable-alistp l)
                       (assoc x l))
                  (eqlablep (car (assoc x l))))))

(local (defthm assoc-eq-properties
         (implies (and (alistp l)
                       (assoc-eq x l))
                  (and (consp (assoc-eq x l))
                       (equal (car (assoc-eq x l)) x)))))

(local (defthm bounded-integer-alistp-eqlable-alistp
         (implies (bounded-integer-alistp l n)
                  (eqlable-alistp l))
         :rule-classes (:rewrite :forward-chaining)))

(local (defthm bounded-integer-alistp-car-assoc-properties
         (implies (and (bounded-integer-alistp l n)
                       (assoc i l)
                       (not (equal (car (assoc i l)) :header)))
                  (and (integerp (car (assoc i l)))
                       (>= (car (assoc i l)) 0)
                       (< (car (assoc i l)) n)))))


;;;****************************************************************************
;;;
;;;    Local array1 events.
;;;
;;;****************************************************************************

;;;  We prove a :FORWARD-CHAINING lemma for ARRAY1P and a couple of other
;;;  LOCAL lemmas, then disable ARRAY1P.  Note that for external consumption
;;;  we provide a :FORWARD-CHAINING lemma written in terms of HEADER,
;;;  DIMENSIONS, MAXIMUM-VALUE, etc.  DON'T MESS WITH THIS ARRANGEMENT, or
;;;  you'll be very frustrated and very sorry!

(local
 (defthm array1p-forward-local
   (implies
    (array1p name l)
    (and
     (symbolp name)
     (alistp l)
     (keyword-value-listp (cdr (assoc-eq :header l)))
     (true-listp
      (cadr (assoc-keyword :dimensions (cdr (assoc-eq :header l)))))
     (equal
      (length (cadr (assoc-keyword :dimensions (cdr (assoc-eq :header l)))))
      1)
     (integerp
      (car (cadr (assoc-keyword :dimensions (cdr (assoc-eq :header l))))))
     (integerp
      (cadr (assoc-keyword :maximum-length (cdr (assoc-eq :header l)))))
     (< 0
	(car (cadr (assoc-keyword :dimensions (cdr (assoc-eq :header l))))))
     (<= (car (cadr (assoc-keyword :dimensions (cdr (assoc-eq :header l)))))
	 (cadr (assoc-keyword :maximum-length (cdr (assoc-eq :header l)))))
     (<= (cadr (assoc-keyword :maximum-length (cdr (assoc-eq :header l))))
	 *maximum-positive-32-bit-integer*)
     (bounded-integer-alistp
      l
      (car (cadr (assoc-keyword :dimensions (cdr (assoc-eq :header l))))))))
   :rule-classes :forward-chaining))

(local (defthm array1p-header-exists
         (implies (array1p name l)
                  (assoc-eq :header l))))

; ARRAY1P-CONS (in a slightly different format) is part of the
; BOOT-STRAP-THEORY of ACL2.

(local (defthm our-array1p-cons
         (implies (and (array1p name l)
                       (integerp n)
                       (>= n 0)
                       (< n (car (dimensions name l))))
                  (array1p name (cons (cons n x) l)))))

(local (in-theory (disable array1p)))

;;;  Now, we prove everthing we need to know about COMPRESS11, and then use
;;;  these lemmas to characterize COMPRESS1.

(local (defthm eqlable-alistp-compress11
         (implies (and (array1p name l)
                       (integerp i)
                       (integerp n)
                       (<= i n))
                  (eqlable-alistp (compress11 name l i n default)))))

(local (defthm bounded-integer-alistp-compress11
         (implies (and (array1p name l)
                       (integerp i)
                       (integerp n)
                       (>= i 0)
                       (<= i n))
                  (bounded-integer-alistp (compress11 name l i n default) n))))

(local (defthm compress11-assoc-property-0
         (implies (and (array1p name l)
                       (integerp i)
                       (integerp n)
                       (<= i n)
                       (integerp j)
                       (assoc j l)
                       (assoc j (compress11 name l i n default)))
                  (equal (assoc j (compress11 name l i n default))
                         (assoc j l)))))

(local (defthm compress11-assoc-property-1
         (implies (and (array1p name l)
                       (not (assoc j (compress11 name l i n default))) ;Free vars!
                       (integerp i)
                       (integerp n)
                       (<= i n)
                       (integerp j)
                       (<= i j)
                       (< j n)
                       (assoc j l))
                  (equal (cdr (assoc j l))
                         default))))

(local (defthm compress11-assoc-property-2
         (implies (and (array1p name l)
                       (integerp i)
                       (integerp n)
                       (<= i n)
                       (integerp j)
                       (not (assoc j l)))
                  (not (assoc j (compress11 name l i n default))))))

; Start events added by Matt K. for Version 3.1, 7/1/06, to support proof of
; compress1-assoc-property-0 in light of addition of reverse-sorted and
; unsorted ACL2 arrays.

(local (defthm assoc-revappend-1
         (implies (not (member key (strip-cars alist1)))
                  (equal (assoc key (revappend alist1 alist2))
                         (assoc key alist2)))))

(local (defthm assoc-revappend
         (implies (and (force (no-duplicatesp (strip-cars alist1)))
                       (force (alistp alist1)))
                  (equal (assoc key (revappend alist1 alist2))
                         (or (assoc key alist1)
                             (assoc key alist2))))))

(local (defun ordered-alistp (x)
         (cond ((atom x)
                (null x))
               ((atom (cdr x))
                (and (consp (car x))
                     (rationalp (caar x))
                     (null (cdr x))))
               (t (and (consp (car x))
                       (rationalp (caar x))
                       (< (caar x) (caadr x))
                       (ordered-alistp (cdr x)))))))

(local (defthm no-duplicatesp-strip-cars-ordered-alistp-1
         (implies (and (< key (caar x))
                       (ordered-alistp x))
                  (not (member key
                               (strip-cars x))))))

(local (defthm no-duplicatesp-strip-cars-ordered-alistp
         (implies (ordered-alistp x)
                  (no-duplicatesp (strip-cars x)))))

(local (defthm consp-assoc-rewrite
         (implies (and key
                       (assoc key alist))
                  (consp (assoc key alist)))))

(local (defthm car-assoc
         (implies (assoc key alist)
                  (equal (car (assoc key alist))
                         key))))

(local (defthm <-caar-compress11
         (implies (and (< i j)
                       (consp (compress11 name l j n default)))
                  (< i (caar (compress11 name l j n default))))))

(local (defthm ordered-alistp-compress11
         (implies (and (integerp i)
                       (integerp n))
                  (ordered-alistp (compress11 name l i n default)))))

(local (defthm not-member-strip-cars-compress11
         (implies (< i j)
                  (not (member i
                               (strip-cars (compress11 name l j n default)))))))

(local (defthm no-duplicatesp-strip-cars-compress11
         (no-duplicatesp (strip-cars (compress11 name l i n default)))))

; End events added by Matt K. for Version 3.1, 7/1/06, to support proof of
; compress1-assoc-property-0 in light of addition of reverse-sorted and
; unsorted ACL2 arrays.

(local (defthm compress1-assoc-property-0
         (implies (and (array1p name l)
                       (integerp n)
                       (>= n 0)
                       (< n (car (dimensions name l)))
                       (assoc n l)
                       (assoc n (compress1 name l)))
                  (equal (cdr (assoc n (compress1 name l)))
                         (cdr (assoc n l))))))

(local (defthm compress1-assoc-property-1
         (implies (and (array1p name l)
                       (integerp n)
                       (>= n 0)
                       (< n (car (dimensions name l)))
                       (assoc n l)
                       (not (assoc n (compress1 name l))))
                  (equal (cdr (assoc n l))
                         (cadr (assoc-keyword :default (cdr (assoc-eq :header l))))))))

(local (defthm compress1-assoc-property-2
         (implies
          (and (array1p name l)
               (integerp n)
               (>= n 0)
               (< n (car (dimensions name l)))
               (not (assoc n l)))
          (not (assoc n (compress1 name l))))))

(local (defthm header-compress1-crock
         (implies (array1p name l)
                  (equal (assoc-eq :header (compress1 name l))
                         (assoc-eq :header l)))))


; The following two events were added by Matt K. for Version 3.1, 7/1/06, to
; support proof of compress1-assoc-property-0 in light of addition of
; reverse-sorted and unsorted ACL2 arrays.

(local
 (defthm alistp-revappend
   (implies (alistp x)
            (equal (alistp (revappend x y))
                   (alistp y)))))

(local
 (defthm bounded-integer-alistp-revappend
   (implies (bounded-integer-alistp x n)
            (equal (bounded-integer-alistp (revappend x y) n)
                   (bounded-integer-alistp y n)))))


(defsection array1-lemmas
  :parents (array1)
  :short "A @(see theory) of all @(see enable)d rules exported by the @(see
array1) book."

  :long "<p>Note that in order for these rules to be applicable you will first
need to @(see DISABLE) the theory @(see ARRAY1-FUNCTIONS).</p>"

;;;****************************************************************************
;;;
;;;    Exported Events.
;;;
;;;    When new lemmas are added their names must also be added to the theory
;;;    ARRAY1-LEMMAS.
;;;
;;;****************************************************************************

  (defthm array1p-compress1
    (implies (array1p name l)
             (array1p name (compress1 name l)))
    :hints (("Goal"
             :in-theory (enable array1p)
             :use array1p-header-exists)))

  (defthm array1p-compress1-properties
    (implies (array1p name l)
             (and
              (equal (header name (compress1 name l))
                     (header name l))
              (equal (dimensions name (compress1 name l))
                     (dimensions name l))
              (equal (maximum-length name (compress1 name l))
                     (maximum-length name l))
              (equal (default name (compress1 name l))
                     (default name l)))))

; COMPRESS1 is now fully characterized, so we DISABLE it and start proving
; the interesting theorems.

  (local (in-theory (disable compress1)))

  (defthm array1p-aset1
    (implies (and (array1p name l)
                  (integerp n)
                  (>= n 0)
                  (< n (car (dimensions name l))))
             (array1p name (aset1 name l n val))))

  (defthm array1p-aset1-properties
    (implies (and (array1p name l)
                  (integerp n)
                  (>= n 0)
                  (< n (car (dimensions name l))))
             (and (equal (header name (aset1 name l n val))
                         (header name l))
                  (equal (dimensions name (aset1 name l n val))
                         (dimensions name l))
                  (equal (maximum-length name (aset1 name l n val))
                         (maximum-length name l))
                  (equal (default name (aset1 name l n val))
                         (default name l)))))

  (defthm aref1-compress1
    (implies (and (array1p name l)
                  (integerp n)
                  (>= n 0)
                  (< n (car (dimensions name l))))
             (equal (aref1 name (compress1 name l) n)
                    (aref1 name l n))))

  (defthm array1p-acons-properties
    (implies (integerp n)
             (and (equal (header name (cons (cons n val) l))
                         (header name l))
                  (equal (dimensions name (cons (cons n val) l))
                         (dimensions name l))
                  (equal (maximum-length name (cons (cons n val) l))
                         (maximum-length name l))
                  (equal (default name (cons (cons n val) l))
                         (default name l)))))

  (defthm array1p-consp-header
    (implies (array1p name l)
             (consp (header name l)))
    :rule-classes :type-prescription)

  (defthm array1p-car-header
    (implies (array1p name l)
             (equal (car (header name l))
                    :header)))

;  These two theorems for the AREF1-ASET1 cases are used to prove a
;  combined result, and then exported DISABLEd.

  (defthm aref1-aset1-equal
    ;; Note that this rule is exported DISABLEd by default in favor of
    ;; AREF1-ASET1.
    (implies (and (array1p name l)
                  (integerp n)
                  (>= n 0)
                  (< n (car (dimensions name l))))
             (equal (aref1 name (aset1 name l n val) n)
                    val)))

  (defthm aref1-aset1-not-equal
    ;; Note that this rule is exported DISABLEd by default in favor of
    ;; AREF1-ASET1.
    (implies (and (array1p name l)
                  (integerp n1)
                  (>= n1 0)
                  (< n1 (car (dimensions name l)))
                  (integerp n2)
                  (>= n2 0)
                  (< n2 (car (dimensions name l)))
                  (not (equal n1 n2)))
             (equal (aref1 name (aset1 name l n1 val) n2)
                    (aref1 name l n2))))

  (defthm aref1-aset1
    ;; Note that this lemma forces the decision of the equality of n1 and n2.  If
    ;; this causes problems, then DISABLE this lemma and (ENABLE
    ;; AREF1-ASET1-EQUAL AREF1-ASET1-NOT-EQUAL)
    (implies (and (array1p name l)
                  (integerp n1)
                  (>= n1 0)
                  (< n1 (car (dimensions name l)))
                  (integerp n2)
                  (>= n2 0)
                  (< n2 (car (dimensions name l))))
             (equal (aref1 name (aset1 name l n1 val) n2)
                    (if (equal n1 n2)
                        val
                      (aref1 name l n2))))
    :hints (("Goal" :in-theory (disable aref1 aset1))))

  (in-theory (disable aref1-aset1-equal aref1-aset1-not-equal))

;;;  The final form of the :FORWARD-CHAINING lemma for ARRAY1P.

  (defthm array1p-forward-modular
    ;;  Forward Chaining: A forward definition of (ARRAY1P name l), in terms of
    ;;  HEADER, DIMENSIONS, and MAXIMUM-LENGTH.
    ;;
    ;;  Note that ACL2 also defines a lemma ARRAY1P-FORWARD, but that lemma
    ;;  is in terms of the expansions of HEADER, DIMENSIONS, and MAXIMUM-LENGTH.
    ;;
    ;;  One should normaly DISABLE ARRAY1P in favor of this :FORWARD-CHAINING rule.
    ;;  If allowed to open, ARRAY1P can cause severe performance degradation due to
    ;;  its large size and many recursive functions.  This lemma is designed to be
    ;;  used with the ARRAY1-FUNCTIONS theory DISABLEd.
    (implies (array1p name l)
             (and (symbolp name)
                  (alistp l)
                  (keyword-value-listp (cdr (header name l)))
                  (true-listp (dimensions name l))
                  (equal (length (dimensions name l)) 1)
                  (integerp (car (dimensions name l)))
                  (integerp (maximum-length name l))
                  (< 0 (car (dimensions name l)))
                  (<= (car (dimensions name l)) (maximum-length name l))
                  (<= (maximum-length name l) *maximum-positive-32-bit-integer*)
                  (bounded-integer-alistp l (car (dimensions name l)))))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (disable length)))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;  RESET-ARRAY1 name l
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++


;  The proofs for RESET-ARRAY1 require a few LOCAL facts.

(local
 (defthm car-header
   (implies (array1p name l)
            (equal (car (header name l))
                   :header))))

(local
 (defthm array1p-list-header
   (implies (array1p name l)
            (array1p name (list (header name l))))
   :hints (("Goal" :in-theory (enable array1p)))))

(local
 (defthm header-list-header
   (implies (array1p name l)
            (equal (header name (list (header name l)))
                   (header name l)))))

(local
 (defthm dimensions-list-header
   (implies (array1p name l)
            (equal (dimensions name (list (header name l)))
                   (dimensions name l)))))

(local
 (defthm default-cons-header
   (implies (array1p name l)
            (equal (default name (cons (header name l) x))
                   (default name l)))))

(local
 (defthm symbol-alistp-list-header
   (implies (array1p name l)
            (symbol-alistp (list (header name l))))))

(local
 (defthm symbol-alistp-not-assoc-integer
   (implies (and (symbol-alistp l)
                 (integerp i))
            (not (assoc i l)))))

(local
 (defthm symbol-alistp-not-compress11
   (implies (and (symbol-alistp l)
                 (integerp i)
                 (integerp n))
            (not (compress11 name l i n default)))))


;  HEADER, DEFAULT, and DIMENSIONS are characterized, so we DISABLE them.

(local (in-theory (disable header default dimensions)))

(defsection reset-array1
  :parents (array1)
  :short "Clear an 1-dimensional array."
  :long "<p>The function (RESET-ARRAY1 name l) returns a 1-dimensional array
whose alist is simply the HEADER of l.  This has the effect of resetting the
array, i.e., reading the new array at any address will return the default
value.  The implementation is simply to redefine the array as the HEADER of the
old array.  Thus all of the HEADER information is carried over to the new
array.</p>

<p>Note that an alternate definition is available as the lemma
RESET-ARRAY1*.</p>"

  (defun reset-array1 (name l)
    (declare (xargs :guard (array1p name l)))
    (compress1 name (list (header name l)))))

(defsection reset-array1*
  :parents (reset-array1)
  :short "Rewrite: (RESET-ARRAY1 name l) = (LIST (HEADER name l))."
  :long "<p>This definition of RESET-ARRAY1 is logically equivalent to the
actual definition. The actual definition, which includes a COMPRESS1 call, has
the run-time side-effect of re-installing the new array.  The COMPRESS1 is
logically redundant, however.</p>

<p>This lemma is exported DISABLED, however this is the preferred definition to
use to reason about RESET-ARRAY1.</p>"

  (defthm reset-array1*
    (implies (array1p name l)
             (equal (reset-array1 name l)
                    (list (header name l))))
    :hints (("Goal" :in-theory (enable compress1 compress11)))))

;  We can now reason with the simple definition RESET-ARRAY1*.

(local (in-theory (disable reset-array1)))

(defsection-progn reset-array1-lemmas
  :extension reset-array1

  (defthm array1p-reset-array1
    (implies (array1p name l)
             (array1p name (reset-array1 name l))))

  (defthm array1p-reset-array1-properties
    (implies (array1p name l)
             (and (equal (header name (reset-array1 name l))
                         (header name l))
                  (equal (dimensions name (reset-array1 name l))
                         (dimensions name l))
                  (equal (maximum-length name (reset-array1 name l))
                         (maximum-length name l))
                  (equal (default name (reset-array1 name l))
                         (default name l)))))

  (defthm aref1-reset-array1
    (implies (and (array1p name l)
                  (integerp index))
             (equal (aref1 name (reset-array1 name l) index)
                    (default name l)))))

(in-theory (disable reset-array1*))


;;;****************************************************************************
;;;
;;;  Theories
;;;
;;;****************************************************************************

(defsection array1-functions
  :parents (array1)
  :short "A theory of all functions specific to 1-dimensional arrays."
  :long "<p>This theory must be DISABLEd in order for the lemmas exported by
the \"array1\" book to be applicable.</p>"

  (deftheory array1-functions
    '(array1p aset1 aref1 compress1 header dimensions maximum-length
              default reset-array1)))

(deftheory array1-lemmas
  '(array1p-compress1
    array1p-compress1-properties
    array1p-aset1 array1p-aset1-properties
    aref1-compress1 array1p-acons-properties
    array1p-consp-header array1p-car-header
    aref1-aset1 array1p-forward-modular
    array1p-reset-array1 array1p-reset-array1-properties
    aref1-reset-array1))

(defsection array1-disabled-lemmas
  :parents (array1)
  :short "A theory of all rules exported DISABLEd by the \"array1\" book."
  :long "<p>Note that in order for these rules to be applicable you will first
need to disable @(see array1-functions).  Look at the :DOC for each lemma for
an explanation of why the lemma is exported DISABLEd.</p>"

  (deftheory array1-disabled-lemmas
    '(aref1-aset1-equal aref1-aset1-not-equal reset-array1*)))


;;;****************************************************************************
;;;
;;;    DEFARRAY1TYPE
;;;
;;;****************************************************************************

(defsection defarray1type
  :parents (array1)
  :short "Characterize 1-dimensional arrays with a fixed element type."
  :long "<p>Example form:</p>

@({
  (DEFARRAY1TYPE INTEGERP-ARRAY1P INTEGERP)
})

<p>The above example defines a recognizer, INTEGERP-ARRAYP, for 1-dimensional
arrays whose elements are all INTEGERP.</p>

<p>General form:</p>

@({
  (DEF1ARRAYTYPE recognizer predicate
                 &key size doc
                      (aref1-lemma-rule-classes ':REWRITE)
                      (aset1-lemma-rule-classes ':REWRITE))
})

<p>DEFARRAY1TYPE defines a recognizer for 1-dimensional arrays whose elements
are all of a single type.  The recognizer argument is a symbol that is used as
the name of the recognizer.  The predicate argument should be a 1-argument,
unguarded Boolean function that recognizes objects of the desired type.  The
predicate may either be a symbol (the name of the predicate), or a LAMBDA
expression.</p>

<p>If :SIZE is specified it should be a variable-free term that will evaluate
to a positive integer.  If specified, then the recognizer will only recognize
1-dimensional arrays of the given type and of a fixed size.</p>

<p>If :DOC is specified it should be a string, and it will be inserted as the
documentation string in the recognizer.</p>

<p>DEFARRAY1TYPE defines a recognizer:</p>

@({ (recognizer NAME L) })

<p>and proves 4 useful theorems about it.  If the :SIZE is not specified then
the three theorems will be:</p>

@({
  1. (IMPLIES (recognizer NAME L)
              (ARRAY1P NAME L))

  2. (IMPLIES (AND (recognizer NAME L)
                   (INTEGERP N))
              (predicate (AREF1 NAME L N)))

  3. (IMPLIES (AND (recognizer NAME L)
                   (< N (CAR (DIMENSIONS NAME L)))
                   (INTEGERP N)
                   (>= N 0)
                   (predicate VAL))
              (recognizer NAME (ASET1 NAME L N VAL)))

  4. (IMPLIES (recognizer NAME l)
              (recognizer NAME (RESET-ARRAY1 name l)))
})

<p>If :SIZE is specified then the first and third theorems become:</p>

@({
  1. (IMPLIES (recognizer NAME L)
              (AND (ARRAY1P NAME L)
                   (EQUAL (CAR (DIMENSIONS name l))
                          size)))

  3. (IMPLIES (AND (recognizer NAME L)
                   (< N size)
                   (INTEGERP N)
                   (>= N 0)
                   (predicate VAL))
              (recognizer NAME (ASET1 NAME L N VAL)))
})

<p>The first theorem is stored as both :REWRITE and :FORWARD-CHAINING rules.
The :RULE-CLASSES of the second and third lemmas default to :REWRITE, but are
selectable by the user by means of the :AREF1-LEMMA-RULE-CLASSES and
:ASET1-LEMMA-RULE-CLASSSES arguments to DEFARRAY1TYPE (respectively).  If
using :RULE-CLASSES other than :REWRITE the user should bear in mind the
documented restrictions on the applicability of :TYPE-PRESCRIPTION and
:FORWARD-CHAINING rules.  The fourth rule is always a :REWRITE rule.</p>

<p>Note the the recognizer is a very strong recognizer that specifies that the
array alist is a BOUNDED-INTEGER-ALISTP whose elements all satisfy the type
predicate.  The recognizer also specifies that the default element of the array
satisfies the predicate as well.</p>

<p>WARNING: The recognizer is defined in terms of a recursive recognizer, named
@('<recognizer>-FN').  THE RECURSIVE RECOGNIZER SHOULD BE COMPILED BEFORE YOU
TRY TO EXECUTE IT, OR IT MAY CAUSE A STACK OVERFLOW.  Also note that the
recognizer will be DISABLEd after execution of this macro.  The user must
insure that the recognizer remains DISABLEd, otherwise the above lemmas will
never be applied.</p>

<p>DEFARRAY1TYPE proves the generated lemmas in a minimal, ENCAPSULATEd theory
that should guarantee that the proofs always succeed.  If one should encounter
a case where a proof fails (as opposed to a translation or other syntax
failure), please notify the author.</p>")

(defmacro defarray1type
  (recognizer predicate &key
	      size doc
              (aref1-lemma-rule-classes ':REWRITE)
              (aset1-lemma-rule-classes ':REWRITE))

  (declare (xargs :guard (and (symbolp recognizer)
                              (pseudo-termp predicate)
			      (implies doc (stringp doc)))))

  ;;  A form for the size, and function and lemma names.

  (let
    ((size-form (if size size '(CAR (DIMENSIONS NAME L))))
     (recognizer-fn
      (intern-in-package-of-symbol
       (coerce (packn1 (list recognizer '-fn)) 'string)
       recognizer))
     (recognizer-lemma
      (intern-in-package-of-symbol
       (coerce (packn1 (list recognizer '-array1p)) 'string)
       recognizer))
     (aref1-lemma
      (intern-in-package-of-symbol
       (coerce (packn1 (list recognizer '-aref1)) 'string)
       recognizer))
     (aset1-lemma
      (intern-in-package-of-symbol
       (coerce (packn1 (list recognizer '-aset1)) 'string)
       recognizer))
     (reset-array1-lemma
      (intern-in-package-of-symbol
       (coerce (packn1 (list recognizer '-reset-array1)) 'string)
       recognizer)))

    `(ENCAPSULATE ()

       ;;  Set up a theory guaranteed to admit the functions and prove the
       ;;  lemmas.  We assume that the "array1" book has been loaded!

       (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
       (LOCAL (IN-THEORY (DISABLE ARRAY1-FUNCTIONS)))
       (LOCAL (IN-THEORY (ENABLE ARRAY1-LEMMAS)))

       ;;  The recursive recognizer.

       (DEFUN ,recognizer-fn (L N)
	 (DECLARE (XARGS :GUARD T))
	 (COND
	  ((ATOM L) (NULL L))
	  (T (AND (CONSP (CAR L))
		  (LET ((KEY (CAAR L))
			(VAL (CDAR L)))
		    (AND (OR (EQ KEY :HEADER)
			     (AND (INTEGERP KEY)
				  (INTEGERP N)
				  (>= KEY 0)
				  (< KEY N)
				  (,predicate VAL)))
			 (,recognizer-fn (CDR L) N)))))))

       ;; The recognizer.

       (DEFUN ,recognizer (NAME L)
	 ,@(if doc (list doc) nil)
	 (DECLARE (XARGS :GUARD T))
	 (AND (ARRAY1P NAME L)
	      (,recognizer-fn L (CAR (DIMENSIONS NAME L)))
	      (,predicate (DEFAULT NAME L))
	      ,@(if size (list `(EQUAL (CAR (DIMENSIONS NAME L)) ,size))
		  NIL)))

       ;;  Lots of crocks.

       (LOCAL
	(DEFTHM DEFARRAY1TYPE-ASSOC-PROPERTIES
          (IMPLIES (AND (,recognizer-fn L N)
                        (ASSOC I L)
                        (INTEGERP I))
                   (AND (CONSP (ASSOC I L))
                        (INTEGERP (CAR (ASSOC I L)))
                        (>= (CAR (ASSOC I L)) 0)
                        (< (CAR (ASSOC I L)) N)
                        (,predicate (CDR (ASSOC I L)))))))

       (LOCAL
	(DEFTHM DEFARRAY1TYPE-CONS-HEADER
          (IMPLIES (ARRAY1P NAME L)
                   (EQUAL (,recognizer-fn (CONS (HEADER NAME L) X) MAX)
                          (,recognizer-fn X MAX)))))

       (LOCAL
	(DEFTHM DEFARRAY1TYPE-COMPRESS11
          (IMPLIES (AND (,recognizer-fn L N)
                        (INTEGERP I)
                        (INTEGERP N))
                   (,recognizer-fn (COMPRESS11 NAME L I N DEFAULT)
                                   N))))

       (LOCAL
	(DEFTHM DEFARRAY1TYPE-ASET1
	  (IMPLIES (AND (ARRAY1P NAME L)
                        (EQUAL SIZE (CAR (DIMENSIONS NAME L)))
                        (,recognizer-fn L SIZE)
                        (,predicate (DEFAULT NAME L))
                        (INTEGERP N)
                        (,predicate VAL)
                        (NOT (< N 0))
                        (< N SIZE))
                   (,recognizer-fn (ASET1 NAME L N VAL) SIZE))
	  :HINTS (("GOAL" :IN-THEORY (ENABLE COMPRESS1 ASET1)))))

       (LOCAL
	(DEFTHM DEFARRAY1TYPE-RESET-ARRAY1
	  (IMPLIES (ARRAY1P NAME L)
                   (,recognizer-fn (RESET-ARRAY1 NAME L) N))
	  :HINTS (("Goal" :IN-THEORY (ENABLE RESET-ARRAY1*)))))

       ;; The recognizer lemma.

       (DEFTHM ,recognizer-lemma
         (IMPLIES (,recognizer NAME L)
                  (AND (ARRAY1P NAME L)
                       ,@(if size (list `(EQUAL (CAR (DIMENSIONS NAME L)) ,size))
                           NIL)))
         :RULE-CLASSES (:REWRITE :FORWARD-CHAINING))

       ;; AREF1 returns objects of the proper type.

       (DEFTHM ,aref1-lemma
         (IMPLIES (AND (,recognizer NAME L)
                       (INTEGERP N))
                  (,predicate (AREF1 NAME L N)))
         :RULE-CLASSES ,aref1-lemma-rule-classes
         :HINTS (("Goal" :IN-THEORY (ENABLE AREF1))))

       ;;  ASET1 returns arrays of the proper type.

       (DEFTHM ,aset1-lemma
         (IMPLIES (AND (,recognizer NAME L)
                       (< N ,size-form)
                       (INTEGERP N)
                       (>= N 0)
                       (,predicate VAL))
                  (,recognizer NAME (ASET1 NAME L N VAL)))
         :RULE-CLASSES ,aset1-lemma-rule-classes)

       ;;  RESET-ARRAY1 returns arrays of the proper type.

       (defthm ,reset-array1-lemma
	 (implies (,recognizer name l)
                  (,recognizer name (reset-array1 name l))))

       ;;  DISABLE the recognizer.

       (IN-THEORY (DISABLE ,recognizer)))))


