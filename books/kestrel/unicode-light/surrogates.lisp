; UTF-16 surrogate code points
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/hex-char-to-val" :dir :system)
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))

(defund high-surrogatep (code-point)
  (declare (type (integer 0 #x10FFFF) code-point))
  (and (<= #xD800 code-point)
       (<= code-point #xDBFF)))

(defund low-surrogatep (code-point)
  (declare (type (integer 0 #x10FFFF) code-point))
  (and (<= #xDC00 code-point)
       (<= code-point #xDFFF)))

(defund combine-utf-16-surrogates (high-surrogate low-surrogate)
  (declare  (type (integer 0 #x10FFFF) high-surrogate)
            (type (integer 0 #x10FFFF) low-surrogate)
            (xargs :guard (and (high-surrogatep high-surrogate)
                               (low-surrogatep low-surrogate))))
  (+ #x10000
     (logior (ash (logand #b1111111111 high-surrogate) ;10 bits
                  10)
             (logand #b1111111111 low-surrogate) ;10 bits
             )))

(defthm natp-of-combine-utf-16-surrogates
  (natp (combine-utf-16-surrogates high-surrogate low-surrogate))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable combine-utf-16-surrogates))))

(defthm <=-of-combine-utf-16-surrogates
  (<= (combine-utf-16-surrogates high-surrogate low-surrogate)
      #x10FFFF)
  :hints (("Goal" :in-theory (e/d (combine-utf-16-surrogates
                                   <-of-ash-arg1)
                                  (<-of-logior-and-expt-of-2))
           :use (:instance <-of-logior-and-expt-of-2
                           (n 20)
                           (i (LOGAND 1023 LOW-SURROGATE))
                           (j (ash (logand #b1111111111 high-surrogate) 10))))))
