; Hons Sanity Checking
; Copyright (C) 2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

(defun hl-hspace-check-normed (x hs)

; (HL-HSPACE-CHECK-NORMED X HS) --> BOOL
;
; X is any ACL2 Object and HS is a Hons Space.  We return true if it appears
; that X is a normed object, but note that this is a non-recursive check.  In
; static honsing mode, this check requires that the object's address has been
; assigned.

  (declare (type hl-hspace hs))
  #-static-hons
  (cond ((consp x)
         (hl-hspace-honsp x hs))
        ((stringp x)
         (let ((entry (gethash x (hl-hspace-str-ht hs))))
           (and entry
                (eq x entry))))
        ;; All other objects are normed.
        (t t))

  #+static-hons
  (cond ((consp x)
         (hl-hspace-honsp x hs))
        ((stringp x)
         (let ((entry (gethash x (hl-hspace-str-ht hs))))
           (and entry
                (eq x (car entry)))))
        ((symbolp x)
         ;; Make sure it has an address.
         (or (eq x nil)
             (eq x t)
             (if (get (the symbol x) 'hl-static-address)
                 t
               nil)))
        ((and (integerp x)
              (<= hl-minimum-static-int x)
              (<= x hl-maximum-static-int))
         ;; Statically assigned, so okay.
         t)
        ((characterp x)
         ;; Statically assigned, so okay.
         t)
        ((gethash x (hl-hspace-other-ht hs))
         ;; Okay, has an address in OTHER-HT.
         t)
        (t
         ;; Oops, no address
         nil)))

#+static-hons
(defun hl-find-objects-with-index (index hs)
  (declare (Type hl-hspace hs))
  (let ((str-ht   (hl-hspace-str-ht hs))
        (other-ht (hl-hspace-other-ht hs))
        (addr-ht  (hl-hspace-addr-ht hs))
        (acc      nil))
    (maphash (lambda (key val)
               (when (equal index (ccl::%staticp val))
                 (push (list :HONS-STR key val) acc)))
             str-ht)
    (maphash (lambda (key val)
               (when (equal index (ccl::%staticp val))
                 (push (list :HONS-OTHER key val) acc)))
             other-ht)
    (maphash (lambda (key val)
               (when (equal index (ccl::%staticp val))
                 (push (list :HONS-CONS key val) acc)))
             addr-ht)
    acc))

(defun hl-hspace-check-str-ht (hs iacc)
  ;; Ensure every entry in STR-HT is valid.  In static-honsing mode, we also
  ;; accumulate the ccl::%staticp indexes of all STR-HT entries into iacc, so
  ;; that we can later check that SBITS is correct.
  (declare (type hl-hspace hs))
  (format t "; Checking STR-HT~%")
  (let ((str-ht (hl-hspace-str-ht hs)))
    (unless (and (typep str-ht 'hash-table)
                 (equal (hash-table-test str-ht) 'equal))
      (error "Expected STR-HT to be an EQUAL hash table"))
    (maphash
     (lambda (key val)
       (unless (stringp key)
         (error "STR-HT key ~a not a string" key))

       ;; In classic honsing, the str-ht associates strings to their normed
       ;; versions.
       #-static-hons
       (unless (equal key val)
         (error "STR-HT key ~a mismatch with val ~a" key val))

       ;; In static honsing, the str-ht associates each string X to X_C = (NX
       ;; . TRUE-ADDR) where X_C is the static cons that serves as the address
       ;; for the normed version of X, NX is the normed version, and TRUE-ADDR
       ;; is the true address of X_C.
       #+static-hons
       (let ((index (ccl::%staticp val)))
         (unless index
           (error "STR-HT val ~a not a static cons" val))
         (unless (equal key (car val))
           (error "STR-HT key ~a mismatch with val ~a" key val))
         (unless (equal (+ index hl-dynamic-base-addr) (cdr val))
           (error "STR-HT val ~a has index ~a; true addr ~
                   should be ~a"
                  val index (+ index hl-dynamic-base-addr)))
         (push index iacc)))
     str-ht))
  iacc)

#-static-hons
(defun hl-hspace-check-flex-alist (flex-alist cdr)
  ;; Classic honsing only.  Check that all the entries in flex-alist are
  ;; appropriate for a flex-alist with this cdr.
  (cond ((listp flex-alist)
         (progn
           (loop for pair in flex-alist do
                 (unless (consp pair)
                   (error "Flex-alist (alist) entry ~a not a cons" pair))
                 (unless (eql (cdr pair) cdr)
                   (error "Flex-alist (alist) entry ~a bad for cdr ~a" pair cdr)))
           (unless (no-duplicatesp (strip-cars flex-alist))
             (error "Flex-alist (alist) with duplicate cars ~a" flex-alist))))
        ((typep flex-alist 'hash-table)
         (maphash
          (lambda (key val)
            (unless (consp val)
              (error "Flex-alist (ht) val ~a not a cons" val))
            (unless (eq key (car val))
              (error "Flex-alist (ht) key ~a mismatch with val ~a" key val))
            (unless (eql cdr (cdr val))
              (error "Flex-alist (ht) val ~a bad for cdr ~a" val cdr)))
          flex-alist))
        (t
         (error "Flex alist for ~a not an alist or hash table." cdr))))

#-static-hons
(defun hl-hspace-check-ctables (hs)
  (declare (type hl-hspace hs))
  (format t "; Checking CTABLES~%")
  (let ((ctables (hl-hspace-ctables hs)))
    (unless (typep ctables 'hl-ctables)
      (error "Invalid ctables"))
    (let ((nil-ht     (hl-ctables-nil-ht ctables))
          (cdr-ht     (hl-ctables-cdr-ht ctables))
          (cdr-ht-eql (hl-ctables-cdr-ht-eql ctables)))

      (format t "; Checking NIL-HT~%")
      (unless (and (typep nil-ht 'hash-table)
                   (equal (hash-table-test nil-ht) 'eql))
        (error "NIL-HT should be an EQL hash table."))
      (hl-hspace-check-flex-alist nil-ht nil)

      (format t "; Checking CDR-HT~%")
      (unless (and (typep cdr-ht 'hash-table)
                   (equal (hash-table-test cdr-ht) 'eq))
        (error "CDR-HT should be an EQ hash table."))
      (maphash
       (lambda (key val)
         (unless (or (consp key)
                     (symbolp key)
                     (and (stringp key)
                          (hl-hspace-check-normed key hs)))
           (error "CDR-HT key ~a not a cons, symbol, or normed string" key))
         (hl-hspace-check-flex-alist val key))
       cdr-ht)

      (format t "; Checking CDR-HT-EQL~%")
      (unless (and (typep cdr-ht-eql 'hash-table)
                   (equal (hash-table-test cdr-ht-eql) 'eql))
        (error "CDR-HT-EQL should be an EQL hash table."))
      (maphash
       (lambda (key val)
         (unless (or (characterp key)
                     (numberp key))
           (error "CDR-HT-EQL key ~a not a character or number." key))
         (hl-hspace-check-flex-alist val key))
       cdr-ht-eql))))

#+static-hons
(defun hl-hspace-check-other-ht (hs iacc)
  ;; Static honsing only.  Ensure every entry in OTHER-HT is valid.  We also
  ;; accumulate all ccl::%staticp indexes into iacc so we can later check that
  ;; SBITS is correct.
  (declare (type hl-hspace hs))
  (format t "; Checking OTHER-HT~%")
  (let ((other-ht (hl-hspace-other-ht hs)))
    (unless (and (typep other-ht 'hash-table)
                 (equal (hash-table-test other-ht) 'eql))
      (error "Expected OTHER-HT to be an EQL hash table"))
    (maphash
     (lambda (key val)
       (let ((index (ccl::%staticp val)))
         (unless (and (numberp key)
                      (or (not (integerp key))
                          (< key hl-minimum-static-int)
                          (< hl-maximum-static-int key)))
           (error "OTHER-HT shouldn't contain ~a" key))
         (unless index
           (error "OTHER-HT val ~a not a static cons" val))
         (unless (equal key (car val))
           (error "OTHER-HT key ~a mismatch with val ~a" key val))
         (unless (equal (+ index hl-dynamic-base-addr) (cdr val))
           (error "OTHER-HT val ~a has index ~a; true addr should be ~a"
                  val index (+ index hl-dynamic-base-addr)))
         (push index iacc)))
     other-ht))
  iacc)

#+static-hons
(defun hl-hspace-check-addr-ht (hs iacc)
  ;; Static honsing only.  Ensure every ADDR-HT entry is valid; accumulate all
  ;; ccl::%staticp indexes into iacc.
  (declare (type hl-hspace hs))
  (format t "; Checking ADDR-HT~%")
  (let ((addr-ht  (hl-hspace-addr-ht hs))
        (str-ht   (hl-hspace-str-ht hs))
        (other-ht (hl-hspace-other-ht hs)))
    (unless (and (typep addr-ht 'hash-table)
                 (equal (hash-table-test addr-ht) 'eql))
      (error "ADDR-HT should be an EQL hash table"))
    (maphash
     (lambda (key val)
       (let ((index (ccl::%staticp val)))
         (unless (integerp key)
           (error "ADDR-HT key ~a not an integer" key))
         (unless index
           (error "ADDR-HT val ~a not a static cons" val))
         (unless (hl-hspace-check-normed (car val) hs)
           (error "ADDR-HT car of ~a not normed" val))
         (unless (hl-hspace-check-normed (cdr val) hs)
           (error "ADDR-HT cdr of ~a not normed" val))
         (let* ((addr-a     (hl-addr-of (car val) str-ht other-ht))
                (addr-b     (hl-addr-of (cdr val) str-ht other-ht))
                (expect-key (hl-addr-combine* addr-a addr-b)))
           (unless (= key expect-key)
             (error "ADDR-HT key ~a wrong for val ~a~%~
                     addr-a = ~a, addr-b = ~a, expected-key = ~a"
                    key val addr-a addr-b expect-key)))
         (push index iacc)))
     addr-ht))
  iacc)

(defun hl-max-list (x)
  (if (atom x)
      0
    (max (car x)
         (hl-max-list (cdr x)))))

#+static-hons
(defun hl-hspace-main-checks (hs)
  (declare (type hl-hspace hs))

  (let* ((atom-acc nil)
         (atom-acc (hl-hspace-check-str-ht hs atom-acc))
         (atom-acc (hl-hspace-check-other-ht hs atom-acc))

         (cons-acc nil)
         (cons-acc (hl-hspace-check-addr-ht hs cons-acc)))
    (format t "; Checking SBITS~%")
    (let* ((sbits     (hl-hspace-sbits hs))
           (sbits-len (length sbits))
           (atom-max  (hl-max-list atom-acc))
           ;; bit arrays to efficiently check for duplication and
           ;; agreement between consbits and sbits
           (atombits  (make-array (max (+ 1 atom-max) sbits-len)
                                  :element-type 'bit
                                  :initial-element 0))
           (consbits  (make-array sbits-len
                                  :element-type 'bit
                                  :initial-element 0)))

      (loop for index in atom-acc do
            (unless (natp index)
              (error "Index ~a not natural" index))
            (when (and (< index sbits-len)
                       (= (aref sbits index) 1))
              (error "SBITS[~a] is set, but it's just an address cons!" index))
            (unless (= (aref atombits index) 0)
              (error "Index ~a used for multiple atoms" index))
            (setf (aref atombits index) 1))

      (loop for index in cons-acc do
            (unless (natp index)
              (error "Index ~a not natural" index))
            (unless (< index sbits-len)
              (error "Index ~a too big for sbits" index))
            (unless (= (aref atombits index) 0)
              (error "Index ~a used as a cons and atom.  ~a" index
                     (ccl::%static-inverse-cons index)))
            (unless (= (aref consbits index) 0)
              (error "Index ~a used for multiple conses" index))
            (setf (aref consbits index) 1))

      (loop for index below sbits-len do
            (unless (= (aref sbits index) (aref consbits index))
              (error "SBITS mismatch on index ~a" index))))))


(defun hl-hspace-check-persist-ht (hs)
  (declare (type hl-hspace hs))
  (format t "; Checking PERSIST-HT~%")
  (let ((persist-ht (hl-hspace-persist-ht hs)))
    (unless (and (typep persist-ht 'hash-table)
                 (equal (hash-table-test persist-ht) 'eq))
      (error "PERSIST-HT should be an EQ hash table"))
    (maphash
     (lambda (key val)
       (unless (consp key)
         (error "PERSIST-HT key ~a not a cons." key))
       (unless (hl-hspace-check-normed key hs)
         (error "PERSIST-HT key ~a not normed." key))
       (unless (eq val t)
         (error "PERSIST-HT val ~a is not T." val)))
     persist-ht)))

;; We no longer require that this hold of fast alists.
;; (defun hl-cons-listp (x)
;;   (or (atom x)
;;       (and (consp (car x))
;;            (hl-cons-listp (cdr x)))))

(defun hl-hspace-check-fast-alist (alist backing-table hs)
  (unless (and (typep backing-table 'hash-table)
               (equal (hash-table-test backing-table) 'eql))
    (error "FALTABLE val not an EQL hash table"))
  (let ((shadow-ht (make-hash-table :test 'eql
                                    :size (hash-table-size backing-table))))
    (loop do
          (when (atom alist)
            (loop-finish))
          (let ((pair (car alist)))
            (hl-hspace-check-normed (car pair) hs)
            (unless (or (gethash (car pair) shadow-ht)
                        (eq pair (gethash (car pair) backing-table)))
              (error "FAL alist binds ~a to ~a, but backing-table binds it to ~a"
                     (car pair) pair (gethash (car pair) backing-table)))
            (setf (gethash (car pair) shadow-ht) t)
            (setq alist (cdr alist))))))

(defun hl-hspace-check-faltable-slots (hs)
  (let* ((faltable (hl-hspace-faltable hs))
         (table (hl-faltable-table faltable))
         (slot1 (hl-faltable-slot1 faltable))
         (slot2 (hl-faltable-slot2 faltable)))
    (unless (and (typep table 'hash-table)
                 (equal (hash-table-test table) 'eq))
      (error "FALTABLE TABLE should be an EQ hash table."))

    (when (hl-falslot-key slot1)
      (or (not (hl-falslot-uniquep slot1))
          (not (gethash (hl-falslot-key slot1) table))
          (error "FALTABLE SLOT1 is marked as unique but key is bound in TABLE.")))

    (when (hl-falslot-key slot2)
      (or (not (hl-falslot-uniquep slot2))
          (not (gethash (hl-falslot-key slot2) table))
          (error "FALTABLE SLOT2 is marked as unique but key is bound in TABLE.")))

    (when (hl-falslot-key slot1)
      (or (not (eq (hl-falslot-key slot1) (hl-falslot-key slot2)))
          (error "FALTABLE SLOT1/SLOT2 have the same keys!")))))

(defun hl-hspace-check-faltable (hs)
  (declare (type hl-hspace hs))
  (format t "; Checking FAL-HT~%")
  (hl-hspace-check-faltable-slots hs)
  (let ((faltable (hl-hspace-faltable hs)))
    (hl-faltable-maphash (lambda (alist backing-table)
                           (hl-hspace-check-fast-alist alist backing-table hs))
                         faltable)))


(defun hl-hspace-check-norm-cache (hs)
  (declare (type hl-hspace hs))
  (format t "; Checking NORM-CACHE~%")
  (let ((norm-cache (hl-hspace-norm-cache hs)))
    (unless (typep norm-cache 'hl-cache)
      (error "NORM-CACHE not an hl-cache"))

    #-static-hons
    (let ((table (hl-cache-table norm-cache))
          (count (hl-cache-count norm-cache)))
      (unless (and (typep table 'hash-table)
                   (equal (hash-table-test table) 'eq))
        (error "NORM-CACHE table not an EQ hash table"))
      (unless (typep count 'fixnum)
        (error "NORM-CACHE count not a fixnum"))
      (unless (>= count (hash-table-count table))
        (error "NORM-CACHE count does not meet/exceed true count"))
      (maphash
       (lambda (key val)
         (unless (consp key)
           (error "NORM-CACHE entry is not a cons: ~a" key))
         (unless (equal key val)
           (error "NORM-CACHE entry not equal to its value: ~a" key))
         (unless (hl-hspace-honsp val hs)
           (error "NORM-CACHE entry not bound to honsp: ~a" key)))
       table))

    #+static-hons
    (let ((keydata (hl-cache-keydata norm-cache))
          (valdata (hl-cache-valdata norm-cache)))
      (loop for i fixnum below (expt 2 20) do
            (let ((key (aref keydata i))
                  (val (aref valdata i)))
              (unless (or (not key) (consp key))
                (error "NORM-CACHE contains invalid key ~a" key))
              (unless (equal key val)
                (error "NORM-CACHE key ~a mismatch with val ~a" key val))
              (unless (or (not val) (hl-hspace-honsp val hs))
                (error "NORM-CACHE val ~a is not honsed" val)))))))


(defun hl-hspace-check-invariants (hs)
  (declare (type hl-hspace hs))

  #-static-hons (progn (hl-hspace-check-str-ht hs nil)
                       (hl-hspace-check-ctables hs))

  #+static-hons (hl-hspace-main-checks hs)

  (hl-hspace-check-persist-ht hs)
  (hl-hspace-check-faltable hs)
  (hl-hspace-check-norm-cache hs)

  nil)


(defun hons-check ()
  (hl-maybe-initialize-default-hs)
  (time$ (hl-hspace-check-invariants *default-hs*))
  nil)
