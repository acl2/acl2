; BV Lists Library: len-mult-of-8p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/ceiling"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../lists-light/len"))
(local (include-book "../lists-light/cons"))

;gen the 8?
(defund len-mult-of-8p (x)
  (declare (xargs :guard (true-listp x)))
  (equal 0 (mod (len x) 8)))

(defthm len-mult-of-8p-of-nthcdr-of-8
  (implies (len-mult-of-8p bits)
           (len-mult-of-8p (nthcdr 8 bits)))
  :hints (("Goal" :in-theory (enable len-mult-of-8p len-of-cdr))))

(defthm len-mult-of-8p-and-consp-forward
  (implies (and (len-mult-of-8p bits)
                (consp bits))
           (<= 8 (len bits)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable len-mult-of-8p))))

(defthm floor-of-len-when-len-mult-of-8p-cheap
  (implies (len-mult-of-8p x)
           (equal (floor (len x) 8)
                  (/ (len x) 8)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable len-mult-of-8p))))

(defthm ceiling-of-len-when-len-mult-of-8p-cheap
  (implies (len-mult-of-8p x)
           (equal (ceiling (len x) 8)
                  (/ (len x) 8)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor len-mult-of-8p floor-when-mod-0))))
