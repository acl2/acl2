; fast-coerce.lisp
; Copyright (C) 2008 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

; This is a sometimes-faster version of coerce.
;
;  - It is the same as ACL2's regular coerce when converting character lists
;    into strings.
;
;  - It is sometimes faster when converting strings into character lists.
;
;      "Fast-coerce is _____ than regular coerce"
;
;       - Allegro: negligibly faster
;       - Clisp:   negligibly slower
;       - GCL:     50-60% faster
;       - CMUCL:   40% faster & uses 30% less memory
;       - SBCL:    50% faster & uses 8% less memory
;       - Old CCL: 90% faster & uses 56% less memory
;       - New CCL: 18% slower
;
; We would like to tailor the :exec part of the definition to fit the Lisp we
; are using via features, but we think this would break the ability to share
; certificates across Lisps.  Ugh.  For now we are just going to leave it as
; is, and say don't use it if your primary environment is the new version of
; CCL.
;
; Ideally we should get rid of this file and simply improve each Lisp.
;
; On Nemesis. (32-bit) -- fast-coerce -------- coerce ------
;
; /p/bin/acl2               10.6s                27s
;
; /p/bin/acl2-allegro       46.4s               48.5s
;                          1.040 GB            1.040 GB
;
; /p/bin/acl2-cmucl         10.3s               17.1s
;                          1.040 GB            1.440 GB
;
; /p/bin/acl2-clisp         44.35s              42.6s
;                          1.040 GB            1.040 GB
;
; On Lhug-3. (64-bit) --- fast-coerce -------- coerce ------
;
;
; /p/bin/acl2-gcl           18.8s               39.7s
;
; /p/bin/acl2-openmcl        5.5s                64s     (OLDER VERSION)
;                          2.080 GB            4.64 GB
;
; /p/bin/acl2-sbcl           5.6s               10.94s
;                          2.080 GB            2.240 GB
;
;
; On FV-1 (64-bit)   --- fast-coerce -------- coerce ------
;
; acl2-ccl                  4.96s              4.07s    (NEW VERSION)
;                          2.080 GB           2.080 GB

#||

(time$ (loop for i fixnum from 1 to 10000000 do
             (coerce "Hello, World!" 'list)))

(time$ (loop for i fixnum from 1 to 10000000 do
             (fast-coerce "Hello, World!" 'list)))

||#

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

(defund fast-coerce-aux1 (x i len)
  (declare (type string x)
           (type (signed-byte 30) i)
           (type (signed-byte 30) len)
           (xargs :guard (and (stringp x)
                              (natp i)
                              (natp len)
                              (= len (length x))
                              (<= i len))
                  :measure (nfix (- (nfix len) (nfix i)))))
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (= (the-fixnum i)
                    (the-fixnum len)))
      nil
    (cons (the character
               (char (the string x)
                     (the (signed-byte 30) i)))
          (fast-coerce-aux1 x
                            (the-fixnum
                             (+ (the-fixnum 1)
                                (mbe :logic (nfix i)
                                     :exec (the-fixnum i))))
                            (the-fixnum len)))))

(defund fast-coerce-aux2 (x i len)
  (declare (type string x)
           (type integer i)
           (type integer len)
           (xargs :guard (and (stringp x)
                              (natp i)
                              (natp len)
                              (= len (length x))
                              (<= i len))
                  :guard-debug t
                  :measure (nfix (- (nfix len) (nfix i)))))
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (= (the integer i) (the integer len)))
      nil
    (cons (char x i)
          (fast-coerce-aux2 x
                            (+ (the integer 1)
                               (mbe :logic (nfix i)
                                    :exec (the integer i)))
                            len))))

(local (defthm lemma
          (implies (and (natp i)
                        (< i (len x)))
                   (equal (cons (nth i x)
                                (cdr (nthcdr i x)))
                          (nthcdr i x)))))

(local (defthm lemma2
         (equal (nthcdr i (cdr x))
                (cdr (nthcdr i x)))))

(local (defthm lemma3
         (implies (and (stringp x)
                       (natp i)
                       (<= i (length x)))
                  (equal (fast-coerce-aux2 x i (len (coerce x 'list)))
                         (nthcdr i (coerce x 'list))))
         :hints(("Goal"
                 :in-theory (enable fast-coerce-aux2)))))

(local (defthm fast-coerce-aux2-equiv
         (equal (fast-coerce-aux1 x i len)
                (fast-coerce-aux2 x i len))
         :hints(("Goal" :in-theory (enable fast-coerce-aux2
                                           fast-coerce-aux1)))))

(defun fast-coerce (x y)
  (declare (xargs :guard (case y
                           (list (stringp x))
                           (string (character-listp x)))))
  (mbe :logic (coerce x y)
       :exec
       ;; I'd like to just use
       ;;  (if (eq y 'list)
       ;;     (coerce x 'list)
       ;;    (coerce x 'string))
       ;; when running on CLISP or CCL, and the loop below for other Lisps.  But
       ;; this would break certificate-compatibility, so I just leave it as is.
       (if (eq y 'list)
           (let ((length (length x)))
             (if (< (the integer length)
                    (the integer 536870912))
                 (fast-coerce-aux1 (the string x)
                                   (the (signed-byte 30) 0)
                                   (the (signed-byte 30) length))
               (fast-coerce-aux2 (the string x)
                                 (the integer 0)
                                 (the integer length))))
         (coerce x y))))

