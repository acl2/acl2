; Serializing ACL2 Objects
; Copyright (C) 2009 by Centaur Technology 
;
; Contact: Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "SERIALIZE")

(declaim (optimize (speed 3) (safety 0) (space 0)))

; In verbose-mode, we print various messages and timing information.

(defparameter *verbose* nil)

(defmacro maybe-time (form)
  `(if *verbose* 
       (time ,form)
     ,form))

(defmacro maybe-print (msg &rest args)
  `(when *verbose*
     (format t ,msg . ,args)))



; ENCODING AND DECODING.
;
; Our encoding functions all operate by writing one byte at a time.  This is
; always done using the encoder-write macro, below, so that we can easily
; change how the writing is done.  (For instance, if block-writes turn out to
; be more efficient than calling write-byte repeatedly, we may wish to change
; encoder-write to write elements into an array, and dump it out when it gets
; filled up.  I haven't bothered to look at this, because most of the time is
; spent in gather-atoms anyway.)
;
; Similarly, our decoding functions operate by reading a byte at a time.  This
; is always done using the decoder-read macro.  
;
;   - On CCL (other than Windows, where CCL:MAP-FILE-TO-OCTET-VECTOR is
;     undefined), we optimize decoder-read by using memory-mapped files.  The
;     variable *decode-vec* holds the contents of the file, while *decode-pos*
;     is our current position while reading the file.  This provides a (very
;     modest) improvement.
;
;   - On other Lisps, we use an ordinary stream, *decode-stream*, and read 
;     from it using read-byte.

(defparameter *encode-stream* nil)

(defmacro encoder-write (x)
  `(write-byte (the (unsigned-byte 8) ,x)
               *encode-stream*))

#-(and ccl (not mswindows))
(progn
  (defparameter *decode-stream* nil)
  (defmacro decoder-read ()
    `(the (unsigned-byte 8) (read-byte *decode-stream*))))

#+(and ccl (not mswindows))
(progn
  (defparameter *decode-vec* nil)
  (defparameter *decode-pos* nil)
  (declaim (type simple-array *decode-vec*))
  (declaim (type fixnum *decode-pos*))
  (defmacro decoder-read ()
    `(let ((ret (the (unsigned-byte 8)
                  (aref (the simple-array *decode-vec*)
                        (the fixnum *decode-pos*)))))
       (incf *decode-pos*)
       ret)))



; Decoder Array.
;
; The encoder mainly operates by writing lists of same-typed objects into the
; file.  The decoder then reads these lists of same-typed objects and puts them
; into an array, the *decode-array*.  The *decode-free* variable says where the
; next available slot in the array is located.

(defvar *decode-array*)
(defparameter *decode-free* 0)
(declaim (type simple-vector *decode-array*))
(declaim (type fixnum *decode-free*))





(declaim (inline nat-byte-decode))

(defun nat-byte-encode (n)
  (declare (type integer n))

; Probably any encoding scheme for ACL2 objects needs to begin with a way to
; handle natural numbers.  Since naturals can be of arbitrary size, this means
; either (1) coming up with a variable-width encoding, or (2) putting an
; artificial limit on the maximum size of naturals that you can support.  Such
; a limit could be very large, e.g., "we won't tolerate numbers which have more
; than 2^64 bits," but it is still sort of ugly.  I prefer to use a variable
; width encoding.
;
; I originally developed a scheme where numbers were split into 64-bit blocks.
; The most-significant bit of the block was used to say whether more blocks
; belonged to the number, and the remaining 63-bits contained the actual bits
; making up the number.  I was thinking this would be good, because even large
; numbers could be represented with overhead of 1/64 their length.
;
; In retrospect, this seems silly.  It seems much more important to be able to
; efficiently record small numbers, such as the lengths of strings and symbols,
; rather than to efficiently deal with large numbers.
;
; I now use a much simpler scheme, based on 8-bit blocks with the
; most-significant bit saying whether or not more blocks are required, and the
; remaining seven bits being the contents of the number.  This imposes an
; overhead of 1/8 the bit length of a number, but I think that's tolerable, and
; I think this probably is a good solution in general."
  
  (if (< n 128)
      (encoder-write n)
    (let ((low  (the (unsigned-byte 8) (logand (the integer n) #x7F)))
          (high (the integer (ash (the integer n) -7))))
      (encoder-write
       (the (unsigned-byte 8)
         (logior (the (unsigned-byte 8) low) #x80)))
      (nat-byte-encode high))))

(defun nat-byte-decode ()
  (let ((shift 0)
        (value 0)
        (x1    (decoder-read)))
    ;; Note: the fixnum declaration of shift may be unsound if integers can
    ;; have more than the maximum fixnum's worth of bits.
    (declare (type fixnum shift)
             (type (unsigned-byte 8) x1)
             (type integer value))
    (loop while (>= x1 128)
          do
          (incf value (ash (- x1 128) shift))
          (incf shift 7)
          (setf x1 (decoder-read)))
    (incf value (ash x1 shift))
    value))

(defun nat-list-byte-encode (x)

; To encode a list of natural numbers, we just write down the length of the
; list, followed by the elements of the list.  In general, this scheme of first
; writing down the number of elements to come, then writing down the elements
; themselves, is something we will do over and over again.

  (let ((len (length x)))
    (maybe-print "; Encoding ~a naturals.~%" len)
    (nat-byte-encode len)
    (dolist (elem x)
      (nat-byte-encode elem))))

(defun nat-list-byte-decode/load ()
  (let ((len (nat-byte-decode)))
    (maybe-print "; Decoding ~a naturals.~%" len)
    (loop for i from 1 to len 
          do
          (setf (svref *decode-array* *decode-free*)
                (nat-byte-decode))
          (incf *decode-free*))))



(declaim (inline rational-byte-encode
                 rational-byte-decode))

(defun rational-byte-encode (x)
  (declare (type rational x))

; We can write down a rational number by first writing its sign, then its
; numerator, then its denominator.  Lists of rationals are handled like lists
; of naturals, by first writing down the length, then writing down the elements
; in the list.

  (nat-byte-encode (if (< x 0) 1 0))
  (nat-byte-encode (abs (numerator x)))
  (nat-byte-encode (denominator x)))

(defun rational-byte-decode ()
  (let* ((sign        (nat-byte-decode))
         (numerator   (nat-byte-decode))
         (denominator (nat-byte-decode)))
    (the rational
      (/ (if (= (the integer sign) 1)
             (- (the integer numerator))
           (the integer numerator))
         (if (= (the integer denominator) 0)
             (error "Trying to decode rational, but denominator is zero.")
           (the integer denominator))))))



(defun rational-list-byte-encode (x)
  (let ((len (length x)))
    (maybe-print "; Encoding ~a rationals.~%" len)
    (nat-byte-encode len)
    (dolist (elem x)
      (rational-byte-encode elem))))

(defun rational-list-byte-decode/load ()
  (let ((len (nat-byte-decode)))
    (maybe-print "; Decoding ~a rationals.~%" len)
    (loop for i from 1 to len 
          do
          (setf (svref *decode-array* *decode-free*)
                (rational-byte-decode))
          (incf *decode-free*))))



(declaim (inline complex-byte-encode
                 complex-byte-decode))

(defun complex-byte-encode (x)
  (declare (type complex x))

; We can write down a complex rational by first writing down its real part,
; then writing down its imaginary part.  Lists of complex rationals can be
; handled like naturals and rationals, by writing down the length and then each
; element.

  (rational-byte-encode (realpart x))
  (rational-byte-encode (imagpart x)))

(defun complex-byte-decode ()
  (let ((realpart (rational-byte-decode))
        (imagpart (rational-byte-decode)))
    (complex (the rational realpart)
             (if (= (the rational imagpart) 0)
                 (error "Trying to decode complex, but imagpart is zero.")
               (the rational imagpart)))))


(defun complex-list-byte-encode (x)
  (let ((len (length x)))
    (maybe-print "; Encoding ~a complexes.~%" len)
    (nat-byte-encode len)
    (dolist (elem x)
      (complex-byte-encode elem))))

(defun complex-list-byte-decode/load ()
  (let ((len (nat-byte-decode)))
    (maybe-print "; Decoding ~a complexes.~%" len)
    (loop for i from 1 to len
          do
          (setf (svref *decode-array* *decode-free*)
                (complex-byte-decode))
          (incf *decode-free*))))



(defun char-list-byte-encode (x)

; We probably could just piggy-back on the natural list encoder, but we go
; ahead and write out characters as the plain bytes for their codes.  This
; might have some trivial advantage w.r.t. encoding characters above 128, but
; that's almost surely unimportant.

  (let ((len (length x)))
    (maybe-print "; Encoding ~a characters.~%" len)
    (nat-byte-encode len)
    (dolist (elem x)
      (encoder-write (the (unsigned-byte 8)
                       (char-code (the character elem)))))))
  
(defun char-list-byte-decode/load ()
  (let ((len (nat-byte-decode)))
    (maybe-print "; Decoding ~a characters.~%" len)
    (loop for i from 1 to len 
          do
          (setf (svref *decode-array* *decode-free*)
                (code-char (decoder-read)))
          (incf *decode-free*))))




(declaim (inline string-byte-encode
                 string-byte-decode))

(defun string-byte-encode (x)
  (declare (type string x))

; We encode strings by just encoding their characters.  Lists of strings are
; handled just like lists of naturals, rationals, and complexes.  We just write
; the length of the list, then write its members.

  (let ((len (length x)))
    ;; NOTE: this declaration might be unsound if strings longer than fixnums
    ;; are possible.
    (declare (type fixnum len))
    (nat-byte-encode len)
    (let ((len-1 (- len 1)))
      (declare (type fixnum len-1))
      (loop for n fixnum from 0 to len-1 do
            (encoder-write 
             (the (unsigned-byte 8)
               (char-code (the character (char x n)))))))))

(defun string-byte-decode ()
  (let* ((len   (nat-byte-decode))
         (len-1 (- len 1))
         (str   (make-string (the fixnum len))))
    (declare (type fixnum len)
             (type fixnum len-1)
             (type vector str))
    (loop for i fixnum from 0 to len-1
          do
          (setf (schar str i)
                (the character 
                  (code-char (decoder-read)))))
    str))

(defun string-list-byte-encode (x)
  (let ((len (length x)))
    (maybe-print "; Encoding ~a strings.~%" len)
    (nat-byte-encode len)
    (dolist (elem x)
      (string-byte-encode elem))))

(defun string-list-byte-decode/load ()
  (let ((len (nat-byte-decode)))
    (maybe-print "; Decoding ~a strings.~%" len)
    (when (> len most-positive-fixnum)
      (error "Too many strings~%"))
    (loop for i fixnum from 1 to len
          do
          (setf (svref *decode-array* *decode-free*)
                (string-byte-decode))
          (incf *decode-free*))))



(defun symbol-list-byte-encode (pkg x)
  (declare (type string pkg))

; We don't want to pay the price of writing down the package for every symbol
; individually, since most of the time an object will probably contain lots of
; symbols from the same package.  So, our basic approach is to organize the
; symbols into groups by their package names, and then for each package we
; write out: the name of the package, and the list of symbol names.  
;
; This function should be given PKG, the name of the package these symbols are
; coming from, and X, the list of symbols that live in this package.
  
  (let ((len (length x)))
    (maybe-print ";; Encoding ~a symbols for ~a package.~%" len pkg)
    (string-byte-encode pkg)
    (nat-byte-encode (length x))
    (dolist (elem x)
      (string-byte-encode (symbol-name elem)))))

(defun symbol-list-byte-decode/load ()
  (let* ((pkg-name (string-byte-decode))
         (len      (nat-byte-decode))
         (stop     (the fixnum (+ *decode-free* len))))
    (maybe-print ";; Decoding ~a symbols for ~a package.~%" len pkg-name)
    ;; We call pkg-witness to ensure the package is known to ACL2, and to 
    ;; justify our use of raw intern below.
    (acl2::pkg-witness pkg-name)
    (loop until (= (the fixnum *decode-free*)
                   (the fixnum stop))
          do
          (setf (svref *decode-array* *decode-free*)
                (intern (string-byte-decode) pkg-name))
          (incf *decode-free*))))

(defun symbol-package-alist-byte-encode (alist)
  
; Alist is an alist mapping package-names to lists of symbols.
  (let ((len (length alist)))
    (maybe-print "; Encoding symbols for ~a packages.~%" len)
    (nat-byte-encode (length alist))
    (dolist (entry alist)
      (symbol-list-byte-encode (car entry) (cdr entry)))))

(defun symbol-package-alist-byte-decode/load ()
  (let ((len (nat-byte-decode)))
    (maybe-print "; Decoding symbols for ~a packages.~%" len)
    (when (> len most-positive-fixnum)
      (error "Too many packages.~%"))
    (loop for i fixnum from 1 to len
          do
          (symbol-list-byte-decode/load))))


(defun inst-list-byte-encode (x)
  
; X is a list of instructions, which are (nat . nat) pairs.

  (let ((len (length x)))
    (maybe-print "; Encoding ~a consing instructions.~%" len)
    (nat-byte-encode len)
    (dolist (elem x)
      (nat-byte-encode (car elem))
      (nat-byte-encode (cdr elem)))))

(defun inst-list-byte-decode/load (honsp)
  #-ccl (when (eq honsp :static)
          (setq honsp nil))
  (let ((len (nat-byte-decode)))
    (when (> len most-positive-fixnum)
      (error "Too many conses"))
    (maybe-print "; Decoding ~a consing instructions.~%" len)
    (cond #+ccl
          ((eq honsp :static) ; ccl only
           (progn 
             (maybe-print ";; Building static conses.~%")
             (loop for i fixnum from 1 to len do
                   (let* ((car-index (nat-byte-decode))
                          (cdr-index (nat-byte-decode))
                          (car-obj   (svref *decode-array* car-index))
                          (cdr-obj   (svref *decode-array* cdr-index)))
                     (setf (svref *decode-array* *decode-free*)
                           (ccl::static-cons car-obj cdr-obj))
                     (incf *decode-free*)))))
          ((eq honsp t)
           (progn
             (maybe-print ";; Building honses.~%")
             (loop for i fixnum from 1 to len do
                   (let* ((car-index (nat-byte-decode))
                          (cdr-index (nat-byte-decode))
                          (car-obj   (svref *decode-array* car-index))
                          (cdr-obj   (svref *decode-array* cdr-index)))
                     (setf (svref *decode-array* *decode-free*)
                           (hons car-obj cdr-obj))
                     (incf *decode-free*)))))
          (t
           (progn
             (maybe-print ";; Building regular conses.~%")
             (loop for i fixnum from 1 to len do
                   (let* ((car-index (nat-byte-decode))
                          (cdr-index (nat-byte-decode))
                          (car-obj   (svref *decode-array* car-index))
                          (cdr-obj   (svref *decode-array* cdr-index)))
                     (setf (svref *decode-array* *decode-free*)
                           (cons car-obj cdr-obj))
                     (incf *decode-free*))))))))
      







; COMPRESSION.
;
; Given a valid ACL2 object, (gather-atoms x) quickly collects a list of all
; the atoms in the object, without duplication.  
;
; The atoms are partitioned into lists by their types, so that we separately
; return the symbols, naturals, non-natural rationals, strings, and finally
; characters found in the object.
;    
; Our implementation involves four hash tables, each of which only associates
; some keys with T.
;
;  - The SYM hash table is used to store symbols we have seen
;  - The EQL hash table is used to store numbers and characters
;  - The STRING hash table is used to store strings
;  - The CONS hash table is used to store conses 
;
; Invariant 1.  Every symbol we have seen is in the SYM hash table.
; Invariant 2.  Every number/character we have seen is in the EQL hash table.
;
; Invariant 3.  The string table is an EQ table that has every string we have
;               seen.  This is only used as a filter to avoid adding some
;               repeated strings into *gathered-strings*, and is NOT COMPLETE
;               since, e.g., "foo" and "foo" may be EQUAL-but-not-EQ.  (We
;               originally used an EQUAL hash table, but found its performance
;               to be too poor.)
;
; We make no guarantees about the CONS hash table; it is used only to avoid
; revisiting shared structures.  It is "safe" to visit an EQUAL-but-not-EQ cons
; repeatedly, because the invariants above ensure that we will not duplicate
; any atoms in our answer.

(defvar *gather-atoms-seen-sym*)
(defvar *gather-atoms-seen-eql*)
(defvar *gather-atoms-seen-string*)
(defvar *gather-atoms-seen-cons*)

(declaim (type hash-table *gather-atoms-seen-sym*))
(declaim (type hash-table *gather-atoms-seen-eql*))
(declaim (type hash-table *gather-atoms-seen-string*))
(declaim (type hash-table *gather-atoms-seen-cons*))


; Because performance can be very sensitive w.r.t. the size of these hash
; tables, it is best to avoid rehashing altogether.  We occasionally try to
; detect size changes so we can report them to the user.
;
; This is a simple scheme.  We record the sizes of the hash tables when we
; create them.  Then, on each recursive call to gather-atoms, we run our debug
; function below.  Ordinarily this is does nothing but decrease the current
; count.  When the count reaches zero, we check the sizes against what we used
; to think they were.  If any changes are detected, we print a message.  This
; way, the overhead stays very low.

(defparameter *gather-atoms-size-sym* 0)
(defparameter *gather-atoms-size-eql* 0)
(defparameter *gather-atoms-size-string* 0)
(defparameter *gather-atoms-size-cons* 0)
(defparameter *gather-atoms-size-debug-start* 0)
(defparameter *gather-atoms-size-debug-current* 0)
(defparameter *gather-atoms-size-debug-help-printed* nil)

(declaim (type fixnum *gather-atoms-size-sym*))
(declaim (type fixnum *gather-atoms-size-eql*))
(declaim (type fixnum *gather-atoms-size-string*))
(declaim (type fixnum *gather-atoms-size-cons*))
(declaim (type fixnum *gather-atoms-size-debug-start*))
(declaim (type fixnum *gather-atoms-size-debug-current*))

(declaim (inline gather-atoms-size-debug))

(defun gather-atoms-size-debug ()
  (decf *gather-atoms-size-debug-current*)
  (when (= *gather-atoms-size-debug-current* 0)

    ;; Start counting down again.
    (setf *gather-atoms-size-debug-current*
          *gather-atoms-size-debug-start*)

    (when (or (> (hash-table-size *gather-atoms-seen-sym*) *gather-atoms-size-sym*)
              (> (hash-table-size *gather-atoms-seen-eql*) *gather-atoms-size-eql*)
              (> (hash-table-size *gather-atoms-seen-string*) *gather-atoms-size-string*)
              (> (hash-table-size *gather-atoms-seen-cons*) *gather-atoms-size-cons*))
      
      ;; If this is the first time we've seen any resize, print a help message.
      (unless *gather-atoms-size-debug-help-printed*
        (format t ";; Note: hash-table resizes detected.  For better performance, consider ~%")
        (format t ";; larger table sizes.  See :doc SERIALIZE::SERIALIZE.~%")
        (setf *gather-atoms-size-debug-help-printed* t))
    
      (when (> (hash-table-size *gather-atoms-seen-sym*) *gather-atoms-size-sym*)
        (format t ";; Note: symbol-table has grown from ~a to ~a.~%"
                *gather-atoms-size-sym* 
                (hash-table-size *gather-atoms-seen-sym*))
        (setf *gather-atoms-size-sym* 
              (hash-table-size *gather-atoms-seen-sym*)))
      
      (when (> (hash-table-size *gather-atoms-seen-eql*) *gather-atoms-size-eql*)
        (format t ";; Note: number-table has grown from ~a to ~a.~%"
                *gather-atoms-size-eql*
                (hash-table-size *gather-atoms-seen-eql*))
        (setf *gather-atoms-size-eql*
              (hash-table-size *gather-atoms-seen-eql*)))
      
      (when (> (hash-table-size *gather-atoms-seen-string*) 
               *gather-atoms-size-string*)
        (format t ";; Note: string-table has grown from ~a to ~a.~%"
                *gather-atoms-size-string*
                (hash-table-size *gather-atoms-seen-string*))
        (setf *gather-atoms-size-string*
              (hash-table-size *gather-atoms-seen-string*)))

      (when (> (hash-table-size *gather-atoms-seen-cons*) 
               *gather-atoms-size-cons*)
        (format t ";; Note: cons-table has grown from ~a to ~a.~%"
                *gather-atoms-size-cons*
                (hash-table-size *gather-atoms-seen-cons*))
        (setf *gather-atoms-size-cons*
              (hash-table-size *gather-atoms-seen-cons*))))))


; We also use several accumulators to store the atoms we have found.  The
; objects are separated by type and pushed into these accumulators.
;
; The accumulators for naturals, rationals, complexes, strings, and characters
; are simple lists that we push new values into.  Because of the invariants
; above, we can guarantee that our accumulators for naturals, rationals,
; complexes, and characters have no duplicates.  The same is NOT true for
; strings, and because of this we have special handling for them.  (We will not
; have any duplicated EQ strings, but we may have some strings which are
; EQUAL-but-not-EQ).
;
; The symbol accumulator is more complex, and associates packages with the
; lists of symbols that are found in that package.  After this is done, we
; convert the hash table into an alist using a simple maphash.  Because of the
; invariants above, the symbols in the hash table are unique.
 
(defvar *gathered-symbols-ht*)
(defparameter *gathered-symbols-alist* nil)
(defparameter *gathered-naturals* nil)
(defparameter *gathered-rationals* nil)
(defparameter *gathered-complexes* nil)
(defparameter *gathered-chars* nil)
(defparameter *gathered-strings* nil)

(declaim (type hash-table *gathered-symbols-ht*))
(declaim (type list *gathered-symbols-alist*))
(declaim (type list *gathered-naturals*))
(declaim (type list *gathered-ratioanls*))
(declaim (type list *gathered-complexes*))
(declaim (type list *gathered-strings*))
(declaim (type list *gathered-chars*))





(defun gather-atoms (x)

; Note: assumes all of the tables and accumulators above have already been
; initialized.  You should never call this directly.

  (gather-atoms-size-debug)

  (cond ((consp x)
         (unless (gethash x *gather-atoms-seen-cons*)
           (setf (gethash x *gather-atoms-seen-cons*) t)
           (gather-atoms (car x))
           (gather-atoms (cdr x))))
        ((symbolp x)
         (unless (gethash x *gather-atoms-seen-sym*)
           (setf (gethash x *gather-atoms-seen-sym*) t)
           (push x (gethash (symbol-package x) *gathered-symbols-ht*))))
        ((stringp x)
         (unless (gethash x *gather-atoms-seen-string*)
           (setf (gethash x *gather-atoms-seen-string*) t)
           (push x *gathered-strings*)))
        (t
         (unless (gethash x *gather-atoms-seen-eql*)
           (setf (gethash x *gather-atoms-seen-eql*) t)
           (cond ((natp x)
                  (push x *gathered-naturals*))
                 ((characterp x) 
                  (push x *gathered-chars*))
                 ((rationalp x)
                  (push x *gathered-rationals*))
                 ((complex-rationalp x)
                  (push x *gathered-complexes*))
                 (t
                  (error "gather-atoms given non-ACL2 object.")))))))


; Once the atoms have been gathered, we build an atom map.  The atom map is
; intended to be an association from every atom in the object to a unique
; number.
;
; Originally, for efficiency, we split the atom map into three hash tables, one
; for eq, one for eql, and one for equal objects (i.e., strings).  The
; *free-index* parameter is the next free index, and just counts up.  Today, we
; use an EQ hash table for the strings as well.

(defparameter *free-index* 0)
(defvar *atom-map-eq*)
(defvar *atom-map-eql*)
(defvar *atom-map-string*)

(declaim (type integer *free-index*))
(declaim (type hash-table *atom-map-eq*))
(declaim (type hash-table *atom-map-eql*))
(declaim (type hash-table *atom-map-string*))


(defun make-atom-map-for-strings (x)

; Here is the story for strings.
;
; To avoid #'equal hashing, we only used EQ to detect whether strings had
; already been seen when we gathered atoms, so the *gathered-strings* 
; accumulator may have various strings which are EQUAL-but-not-EQ.
;
; We also want to avoid #'equal hashing when we build our consing instructions,
; so we are going to do something special for *atom-map-string*.
;
; This function is called with (sort *gathered-strings*) as its input.  Because
; of that, we only need to look at adjacent strings to see if they are
; EQUAL-but-not-EQ.  We are going to add an entry for every string to
; *atom-map-string*, but we do something tricky: if the string is EQUAL to 
; its neighbor, we do not increment the *free-index*.
;
; In other words, given a list like ("foo" "foo" "bar") of non-EQ strings, we
; will assign the first two "foo"s to the same index, and "bar" to the next
; index.  This way, our make-instructions function can do EQ lookups and yet
; still find the same index for strings.
;
; We construct *atom-map-string* as a side-effect.  We return a version of X
; where all duplicates have been eliminated.  This is important because when we
; encode the strings, they implicitly get indexed, and this indexing needs to
; agree with the values we've assigned in the atom map.

  (if (null x)
      x
    (progn
      ;; In all cases, add an entry for the first string.
      (setf (gethash (first x) *atom-map-string*) *free-index*)
      (if (or (null (cdr x))
              (not (equal (first x) (second x))))
          ;; Not (STR1 STR1 ...), so increment and keep going
          (progn
            (incf *free-index*)
            (cons (car x) 
                  (make-atom-map-for-strings (cdr x))))
        ;; (STR1 STR1 ...), so treat it as (STR1 ...)
        (make-atom-map-for-strings (cdr x))))))



(defun make-atom-map ()

; Note: assumes all of the tables above have already been initialized.  You
; should never call this directly.

; Note: this order must agree with encode-to-file.

  (dolist (elem *gathered-naturals*)
    (setf (gethash elem *atom-map-eql*) *free-index*)
    (incf *free-index*))
  (dolist (elem *gathered-rationals*)
    (setf (gethash elem *atom-map-eql*) *free-index*)
    (incf *free-index*))
  (dolist (elem *gathered-complexes*)
    (setf (gethash elem *atom-map-eql*) *free-index*)
    (incf *free-index*))
  (dolist (elem *gathered-chars*)
    (setf (gethash elem *atom-map-eql*) *free-index*)
    (incf *free-index*))

  ;; Strings get sorted then added with our custom routine.
  (let ((sorted-strings (maybe-time (sort *gathered-strings* #'string<))))
    (setf *gathered-strings* 
          (maybe-time (make-atom-map-for-strings sorted-strings))))

  ;; Turn the hash table of symbols into an alist so that they're in the
  ;; same order now and when we encode.  Probably not necessary?
  (maphash (lambda (key val)
             (push (cons (package-name key) val)
                   *gathered-symbols-alist*))
           *gathered-symbols-ht*)
  (dolist (elem *gathered-symbols-alist*)
    (dolist (sym (cdr elem))
      (setf (gethash sym *atom-map-eq*) *free-index*)
      (incf *free-index*))))


; Once all the atoms have been assigned indices, we are going to create a list 
; of instructions for reassembling the conses in the object.  We keep incrementing
; *free-index* as we go, so that the atoms and conses are in a shared index-space.

; As we walk through X, we construct an eq hash-table that maps the conses in X
; to their indices.  We also accumulate a list of instructions, which are pairs
; of the form (car-index . cdr-index), that will be used to recreate each cons.
; We build this list of instructions in reverse-order using push.

(defvar *cons-table*)
(defparameter *cons-instructions* nil)

(declaim (type hash-table *cons-table*))
(declaim (type list *cons-instructions*))

(defun make-instructions (x)

; We always return the index of our argument.

  (if (atom x)
      (cond ((symbolp x)
             (gethash x *atom-map-eq*))
            ((stringp x)
             (gethash x *atom-map-string*))
            (t
             (gethash x *atom-map-eql*)))
    (or (gethash x *cons-table*)
        (let* ((car-index (make-instructions (car x)))
               (cdr-index (make-instructions (cdr x)))
               (my-index  *free-index*))
          (incf *free-index*)
          (setf (gethash x *cons-table*) my-index)
          (push (cons car-index cdr-index) *cons-instructions*)
          my-index))))


(defun encode-to-file ()

; I actually just make this a function so I can time it easily.

  (nat-list-byte-encode *gathered-naturals*)
  (rational-list-byte-encode *gathered-rationals*)
  (complex-list-byte-encode *gathered-complexes*)
  (char-list-byte-encode *gathered-chars*)
  (string-list-byte-encode *gathered-strings*)
  (symbol-package-alist-byte-encode *gathered-symbols-alist*)
  (inst-list-byte-encode *cons-instructions*))


(defun write-fn (filename obj verbosep symbol-table-size number-table-size
                          string-table-size cons-table-size package-table-size 
                          state)
; X is an ACL2 object to write into filename.

  (let ((*verbose*                  verbosep)
        (*gather-atoms-seen-sym*    (make-hash-table :test 'eq :size symbol-table-size))
        (*gather-atoms-seen-eql*    (make-hash-table :test 'eql :size number-table-size))
        (*gather-atoms-seen-string* (make-hash-table :test 'eq :size string-table-size))
        (*gather-atoms-seen-cons*   (make-hash-table :test 'eq :size cons-table-size))
        (*gathered-symbols-ht*      (make-hash-table :test 'eq :size package-table-size))
        (*gathered-symbols-alist*   nil)
        (*gathered-naturals*        nil)
        (*gathered-rationals*       nil)
        (*gathered-complexes*       nil)
        (*gathered-strings*         nil)
        (*gathered-chars*           nil)
        (*free-index*               0)
        (*atom-map-eq*              (make-hash-table :test 'eq :size symbol-table-size))
        (*atom-map-eql*             (make-hash-table :test 'eql :size number-table-size))
        (*atom-map-string*          (make-hash-table :test 'eq :size string-table-size))
        (*cons-table*               (make-hash-table :test 'eq :size cons-table-size))
        (*cons-instructions*        nil)
        (*encode-stream*            (open filename 
                                          :direction :output
                                          :if-exists :supersede
                                          :element-type '(unsigned-byte 8))))

; At one point I thought it might be useful to declare all of the above as
; dynamic-extent.  But it seems like CCL doesn't stack-allocate hash tables?  I
; wonder if there's a way to tell the garbage collector to ignore these until
; the function is over, and to throw them away afterwards?  Ask Bob?

    (let ((*gather-atoms-size-sym*                (hash-table-size *gather-atoms-seen-sym*))
          (*gather-atoms-size-eql*                (hash-table-size *gather-atoms-seen-eql*))
          (*gather-atoms-size-string*             (hash-table-size *gather-atoms-seen-string*))
          (*gather-atoms-size-cons*               (hash-table-size *gather-atoms-seen-cons*))
          (*gather-atoms-size-debug-help-printed* nil)
          (*gather-atoms-size-debug-start*        60000)
          (*gather-atoms-size-debug-current*      30000))

      (maybe-print "; Table sizes: symbols ~a; numbers ~a; strings ~a; conses ~a; packages ~a.~%"
                   symbol-table-size 
                   number-table-size
                   string-table-size
                   cons-table-size
                   package-table-size)

      (maybe-print "; Gathering atoms.~%")
      (maybe-time (gather-atoms obj))

      (maybe-print "; Making atom map.~%")
      (maybe-time (make-atom-map))

      (maybe-print "; Making instructions.~%")
      (maybe-time (make-instructions obj))
      (setf *cons-instructions* (nreverse *cons-instructions*))

      ;; Do all of the encoding.  We start each file with a 32-bit number,
      ;; #xAC12OBC7, which, squinted at, looks vaguely like "ACL2 OBCT", i.e.,
      ;; "ACL2 Object". This gives us a minor sanity check and ensures that the
      ;; file doesn't start with valid ASCII characters, so programs that convert
      ;; newlines in text-mode files should hopefully leave us alone.
      (encoder-write #xAC)
      (encoder-write #x12)
      (encoder-write #x0B)
      (encoder-write #xC7)

      ;; Number of indices needed in the decode array.
      (maybe-print "; Max index is ~a.~%" *free-index*)
      (nat-byte-encode *free-index*)

      ;; All the contents of the object, put into their types.
      (maybe-time (encode-to-file))

      ;; As a final sanity check, we again write #xAC12OBC7, which we can look
      ;; for as a sanity check.
      (encoder-write #xAC)
      (encoder-write #x12)
      (encoder-write #x0B)
      (encoder-write #xC7)

      ;; All done.
      (close *encode-stream*)

      state)))



(defun check-magic-number (filename)
  (let* ((magic-1 (decoder-read))
         (magic-2 (decoder-read))
         (magic-3 (decoder-read))
         (magic-4 (decoder-read)))
    (unless (and (= magic-1 #xAC)
                 (= magic-2 #x12)
                 (= magic-3 #x0B)
                 (= magic-4 #xC7))
      (error "File ~a does not seem like a serialized ACL2 object." filename))))

(defun decode-and-load (honsp)
  (nat-list-byte-decode/load)
  (rational-list-byte-decode/load)
  (complex-list-byte-decode/load)
  (char-list-byte-decode/load)
  (string-list-byte-decode/load)
  (symbol-package-alist-byte-decode/load)
  (inst-list-byte-decode/load honsp))

(defun actually-read (filename honsp verbosep)

  (let* ((*verbose* verbosep)
         #-(and ccl (not mswindows)) (*decode-stream* nil)
         #+(and ccl (not mswindows)) (*decode-pos* nil)
         #+(and ccl (not mswindows)) (*decode-vec* nil)
         #+(and ccl (not mswindows)) (mapped-file nil)
         )

    (maybe-print "; Opening file.~%")

    ;; Ugly.  In most Lisps, we just use ordinary streams.  In CCL, we use a 
    ;; memory-mapped file.
    #-(and ccl (not mswindows))
    (setf *decode-stream* (open filename 
                                :direction :input
                                :element-type '(unsigned-byte 8)
                                :if-does-not-exist :error))

    #+(and ccl (not mswindows))
    (progn
      (setf mapped-file (ccl::map-file-to-octet-vector filename))
      (multiple-value-bind (arr offset)
          (array-displacement mapped-file)
        ;(format t "Type of arr is ~a" (type-of arr))
        ;(format t "Simple-vectorp is ~a" (typep arr 'simple-vector))
        (setf *decode-pos* offset)
        (setf *decode-vec* arr)))

    (check-magic-number filename)
    (let* ((max-index      (nat-byte-decode))
           (*decode-array* (make-array max-index))
           (*decode-free*  0))
      ;; BOZO is dynamic-extend okay given that we return decode-array[max-index - 1]
      ;; at the end of the loop?  it seems to work okay for the tests at least.
      (declare (dynamic-extent *decode-array*)
               (dynamic-extent *decode-free*))
      (maybe-print "; Max index is ~a.~%" max-index)
      (maybe-time (decode-and-load honsp))
      (check-magic-number filename)
      
      (maybe-print "; Closing file.~%")
      #-(and ccl (not mswindows)) (close *decode-stream*)
      #+(and ccl (not mswindows)) (ccl::unmap-octet-vector mapped-file)

      (maybe-print "; Final sanity check.~%")
      (unless (= *decode-free* max-index)
        (error "File ~a has the wrong number of entries: decode-free is ~a, max-index is ~a.~%"
               filename *decode-free* max-index))

      (svref *decode-array* (- max-index 1)))))

(defun read-fn (filename honsp verbosep state)
  (mv (actually-read filename honsp verbosep) 
      state))






