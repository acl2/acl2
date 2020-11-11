; More theorems about getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "kestrel/utilities/polarity" :dir :system)

(defthm getbit-equal-1-polarity
  (implies (syntaxp (want-to-weaken (equal 1 (getbit n x))))
           (equal (equal 1 (getbit n x))
                  (not (equal 0 (getbit n x))))))

(defthm getbit-equal-1-polarity2
  (implies (syntaxp (want-to-weaken (equal (getbit n x) 1)))
           (equal (equal 1 (getbit n x))
                  (not (equal 0 (getbit n x))))))

(defthm getbit-equal-0-polarity
  (implies (syntaxp (want-to-weaken (equal 0 (getbit n x))))
           (equal (equal 0 (getbit n x))
                  (not (equal 1 (getbit n x))))))

(defthm getbit-equal-0-polarity2
  (implies (syntaxp (want-to-weaken (equal (getbit n x) 0)))
           (equal (equal 0 (getbit n x))
                  (not (equal 1 (getbit n x))))))
