
;  names-and-indices.lisp                      Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; (ld "names-and-indices.lisp" :ld-pre-eval-print t)
; (certify-book "names-and-indices" ?)

(in-package "ACL2")

(include-book "std/util/bstar"    :dir :system)

; For array length issues

(defthm len-of-resize-list
  (equal (len (resize-list lst size init))
         (nfix size)))

(defconst *2^60* (expt 2 60))

(defmacro u60 (x)
  `(the (unsigned-byte 60) ,x))

; Our replacement for ACL2's POSITION function

(defun pos-acc (x l acc)
  (declare (xargs :guard (and (symbolp x)
                              (natp acc)
                              (< (+ acc (len l)) *2^60*))))
  (if (or (atom l)
          (eq x (car l)))
      acc
    (pos-acc x (cdr l) (u60 (1+ (u60 acc))))))

(defthm pos-acc-less-than-len+acc
  (implies (and (natp acc)
                (member-eq x l))
	   (< (pos-acc x l acc) (+ acc (len l))))
  :rule-classes :linear)

(defthm pos-acc-equal-len
  (implies (and (natp acc)
                (not (member-eq x l)))
	   (= (pos-acc x l acc) (+ acc (len l))))
  :rule-classes :linear)

(defthm natp-pos-acc
  (implies (natp acc)
           (natp (pos-acc x l acc)))
  :rule-classes :type-prescription)

(defthm pos-acc-bounds
  (implies (natp acc)
           (<= (pos-acc x l acc)
               (+ acc (len l))))
  :rule-classes :linear)

(in-theory (disable (pos-acc)))

(defun-inline pos (x l)
  (declare (xargs :guard (and (symbolp x)
                              (< (len l) *2^60*))))
  (pos-acc x l 0))

(defthm natp-pos
  (natp (pos x l))
  :rule-classes :type-prescription)

(defthm pos-less-than-len
  (implies (member-eq x l)
	   (< (pos x l) (len l)))
  :rule-classes :linear)

(defthm pos-equal-len
  (implies (not (member-eq x l))
	   (= (pos x l) (len l)))
  :rule-classes :linear)

(defthm pos-bounds
  (<= (pos x l) (len l))
  :rule-classes :linear)

(in-theory (disable pos))

; Move somewhere...

#||
(defun-inline pos (x l)
  (declare (xargs :guard (true-listp l)))
  (position-equal x l))
||#

(defthm position-equal-ac-bounds
  (implies (and (natp acc)
                (position-equal-ac item lst acc))
           (< (position-equal-ac item lst acc)
              (+ (len lst)
                 acc)))
  :rule-classes :linear)

(defthm position-equal-ac-bounds-member-equal
  (implies (and (natp acc)
                (member-equal item lst))
           (< (position-equal-ac item lst acc)
              (+ (len lst)
                 acc))))

(defthm natp-position-equal-ac-member-equal
  (implies (and (natp acc)
                (member-equal item lst))
           (natp (position-equal-ac item lst acc)))
  :rule-classes :type-prescription)

(in-theory (disable position-equal-ac))

(defthm position-equal-bounds
  (implies (and (not (stringp lst))
                (position-equal item lst))
           (< (position-equal item lst)
              (len lst)))
  :rule-classes :linear)

(defthm position-equal-bounds-member-equal
  (implies (member-equal item lst)
           (< (position-equal item lst)
              (len lst)))
  :rule-classes :linear)

(defthm natp-position-equal-member-equal
  (implies (member-equal item lst)
           (natp (position-equal item lst)))
  :rule-classes :type-prescription)

(in-theory (disable position-equal))

#||
(defthm natp-pos
  (implies (pos x l)
           (natp (pos x l))))

(defthm natp-pos-member-equal
  (implies (member-equal x l)
           (natp (pos x l))))

(defthm pos-bounds
  (implies (and (not (stringp lst))
                (pos item lst))
           (< (pos item lst)
              (len lst)))
  :rule-classes :linear)

(defthm pos-bounds-member-equal
  (implies (member-equal item lst)
           (< (pos item lst)
              (len lst)))
  :rule-classes :linear)

(in-theory (disable pos))

||#

; A way to generate a new symbol

; Check for OK names in circuit netlists.

(defun alpha-numeric-p (x)
  (declare (xargs :guard t))
  ;; We choose to allow names in the circuit definition to contain #\-
  ;; and #\+ in native LISP netlists. While parsing a netlist from a
  ;; SPICE file, we disallow the use of #\- and #\+ in names as these
  ;; are interpreted by SPICE as arithmetic operators.

  ;; We don't expect to find any #\- and #\+ symbols from our
  ;; ACL2-based SPICE parser.
  (and (characterp x)
       (standard-char-p x)
       (or (alpha-char-p x)
           (not (null (digit-char-p x 10)))
           (equal x #\_)
           (equal x #\-)
           (equal x #\@)
           (equal x #\+)
           (equal x #\%) ; % is reserved for VWSIM to generate new
                         ; names. Thus, this character is not included
                         ; in the documentation as an allowed
                         ; character for user-defined netlists.
           )))

(defun symlp (symbol)
  "Check for symbol with alphabetic first character."
  (declare (xargs :guard t))
  (and
   (symbolp symbol)
   (b* (((if (booleanp symbol))
         ;; the following cw is repeatedly printed when processing
         ;; subsequent proofs
         nil) ;(cw "symlp: symbol cannot be Boolean (i.e., T or NIL).~%"))
        (symbol-name (symbol-name symbol))
        ((if (zp (length symbol-name)))
         (cw "symlp: zero-length symbol.~%"))
        ((unless (standard-char-listp (coerce symbol-name 'list)))
         (cw "symlp: symbol-name has characters that are not standard-char-p.~%"))
        (first-char (char symbol-name 0))
        ((unless (characterp first-char))
         (cw "symlp: non-CHARACTERP first character.~%"))
        ;; should be taken care of by standard-char-listp
        ((unless (standard-char-p first-char))
         (cw "symlp: non-STANDARD-CHAR-P first character.~%"))
        ((unless (alpha-numeric-p first-char))
         (cw "symlp: non alphanumeric first character.~%"))
        ;; Other checks, such as allowable characters, etc.
        )
     t)))

(defthm symlp-forward-to-symbolp
  (implies (symlp x)
           (and (symbolp x)
                (not (booleanp x))))
  :rule-classes :forward-chaining)

(in-theory (disable symlp))

(defun syml-listp (symbols)
  "Check for list of SYMLP symbols."
  (declare (xargs :guard t))
  (if (atom symbols)
      (null symbols)
    (and (symlp (car symbols))
         (syml-listp (cdr symbols)))))

(defun dp (sym)
  ;; should the guard be symlp or symbolp?
  (declare (xargs :guard (symbolp sym)))
  (let* ((str (symbol-name sym))
         (dp-str (string-append "!" str))
         (new-symbol (intern dp-str "ACL2")))
      new-symbol))

(encapsulate
  ()

; From Matt Kaufmann...

; To prove that (dp sym) is not Boolean, we think about a proof by
; contradiction.  If it were Boolean, then its symbol-name would start
; with #\T or #\N, and not #\!.  That difference in symbol-names is
; exposed by coercing each to a list, where the CARs thus differ.

  (local (defthm not-booleanp-dp-lemma
           (implies (booleanp x)
                    (not (equal (coerce (symbol-name (dp sym)) 'list)
                                (coerce (symbol-name        x) 'list))))
           :hints
           (("Goal" :in-theory (enable booleanp)))
           :rule-classes nil))

  (defthm not-booleanp-dp
    (not (booleanp (dp sym)))
    :hints
    (("Goal" :use ((:instance not-booleanp-dp-lemma
                              (x (dp sym))))))
    :rule-classes :type-prescription))

(in-theory (disable dp))

(defun make-dp-list (sym-list)
  (declare (xargs :guard (syml-listp sym-list)))
  (if (atom sym-list)
      nil
    (cons (dp (car sym-list))
          (make-dp-list (cdr sym-list)))))

(defthm symbol-listp-make-dp-list
  (symbol-listp (make-dp-list sym-list)))

(defthm len-make-dp-list-is-len-sym-list
  (equal (len (make-dp-list sym-list))
         (len sym-list)))

(defthm syml-listp-forward-to-symbol-listp
  (implies (syml-listp list-of-symbols)
           (symbol-listp list-of-symbols))
  :rule-classes :forward-chaining)

(defthm append-syml-listp
  (implies (and (syml-listp lst1)
                (syml-listp lst2))
           (syml-listp (append lst1 lst2))))

(defthm syml-listp-remove-duplicates
  (implies (syml-listp l)
           (syml-listp (remove-duplicates-equal l))))

