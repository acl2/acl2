; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../set")
(include-book "../in")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-nat
  ((max natp) ;; Inclusive
   state)
  :returns (mv (nat natp)
               state)
  (random$ (+ max 1) ;; Exclusive
           state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-integer
  ((min integerp) ;; Inclusive
   (max integerp) ;; Inclusive
   state)
  :guard (<= min max)
  :returns (mv (integer integerp)
               state)
  (b* (((mv nat state)
        (mk-random-nat (- max min) state)))
    (mv (+ nat min)
        state)))

(define mk-random-integer-not-in
  ((min natp)
   (max natp) ;; Inclusive
   (blacklist setp)
   state)
  :guard (<= min max)
  :returns (mv (integer integerp)
               state)
  (b* (((mv integer state)
        (mk-random-integer min max state))
       ((unless (in integer blacklist))
        (mv integer state)))
    (mk-random-integer-not-in min max blacklist state)))

(define mk-random-integer-list
  ((count natp)
   (min integerp) ;; Inclusive
   (max integerp) ;; Inclusive
   (acc integer-listp)
   state)
  :guard (< min max)
  :returns (mv (integer-list integer-listp)
               state)
  (b* (((when (zp count))
        (mv acc state))
       ((mv integer state)
        (mk-random-integer min max state)))
    (mk-random-integer-list (- count 1)
                            min
                            max
                            (cons integer acc)
                            state)))

(define mk-random-integer-list-not-in
  ((count natp)
   (min integerp) ;; Inclusive
   (max integerp) ;; Inclusive
   (blacklist setp)
   (acc integer-listp)
   state)
  :guard (< min max)
  :returns (mv (integer-list integer-listp)
               state)
  (b* (((when (zp count))
        (mv acc state))
       ((mv integer state)
        (mk-random-integer-not-in min max blacklist state)))
    (mk-random-integer-list-not-in (- count 1)
                                   min
                                   max
                                   blacklist
                                   (cons integer acc)
                                   state)))

(define min-list
  ((integers integer-listp))
  :guard (not (endp integers))
  (declare (xargs :type-prescription (integerp (min-list integers))))
  (if (mbt (consp integers))
      (if (endp (rest integers))
          (first integers)
        (acl2::min (first integers)
                   (min-list (rest integers))))
    0))

;; Skewed toward *smaller* values
(define mk-random-integer-skewed
  ((min integerp) ;; Inclusive
   (max integerp) ;; Inclusive
   (samples posp)
   state)
  :guard (<= min max)
  :returns (mv (integer integerp)
               state)
  (b* (((mv integer-list state)
        (mk-random-integer-list samples min max nil state)))
    (mv (min-list integer-list)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes *standard* characters
(define mk-random-character (state)
  :returns (mv (character characterp)
               state)
  (b* (((mv code state)
        ;; Standard character codes are either 10 or in the range: 32-126.
        (mk-random-integer 31 126 state)))
    (mv (if (int= 31 code)
           #\Newline
          (code-char code))
        state)))

(define mk-random-character-list
  ((count natp)
   (acc character-listp)
   state)
  :returns (mv (character-list character-listp)
               state)
  (b* (((when (zp count))
        (mv acc state))
       ((mv char state)
        (mk-random-character state)))
    (mk-random-character-list (- count 1)
                              (cons char acc)
                              state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-string
  ((length natp)
   state)
  :returns (mv (str stringp)
               state)
  (b* (((mv chars state)
        (mk-random-character-list length nil state)))
    (mv (coerce chars 'string)
        state)))

(define mk-random-string-skewed
  (&key
   ((min-length natp) '0)
   ((max-length natp) '1000)
   ((samples posp) '40)
   (state 'state))
  :returns (mv (str stringp)
               state)
  (b* (((mv length state)
        (mk-random-integer-skewed min-length max-length samples state)))
    (mk-random-string length state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-symbol
  ((length natp)
   (witness symbolp)
   state)
  :returns (mv (str stringp)
               state)
  (b* (((mv str state)
        (mk-random-string length state)))
    (mv (intern-in-package-of-symbol str witness)
        state)))

(define mk-random-symbol-skewed
  (&key
   ((min-length natp) '1)
   ((max-length natp) '100)
   ((samples posp) '20)
   ((witness symbolp) ''acl2::acl2-pkg-witness)
   (state 'state))
  :returns (mv (str stringp)
               state)
  (b* (((mv str state)
        (mk-random-string-skewed
          :min-length min-length
          :max-length max-length
          :samples samples)))
    (mv (intern-in-package-of-symbol str witness)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-obj (state)
  :returns (mv obj state)
  (b* (((mv case state)
        (mk-random-nat 3 state)))
    ;; TODO: conses
    ;; TODO: rational, complex numbers
    (case case
      (0 (mk-random-integer -65536 65536 state))
      (1 (mk-random-character state))
      (2 (mk-random-string-skewed))
      (otherwise
        (mk-random-symbol-skewed)))))

(define mk-random-obj-not-in
  ((blacklist setp)
   state)
  :returns (mv obj state)
  (b* (((mv obj state)
        (mk-random-obj state))
       ((unless (in obj blacklist))
        (mv obj state)))
    (mk-random-obj-not-in blacklist state)))

(define mk-random-obj-list-not-in
  ((count natp)
   (blacklist setp)
   (acc integer-listp)
   state)
  :returns (mv (list true-listp)
               state)
  (b* (((when (zp count))
        (mv acc state))
       ((mv obj state)
        (mk-random-obj-not-in blacklist state)))
    (mk-random-obj-list-not-in (- count 1)
                               blacklist
                               (cons obj acc)
                               state)))
