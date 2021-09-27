; A recognizer for lists of signed bytes.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sequences/defforall" :dir :system)

;it's a bit odd to say (signed-byte-p size lst) since the second arg is actually the successive cars of lst
(defforall all-signed-byte-p (size lst) (signed-byte-p size lst) :fixed size :declares ((type t size lst)))

(defthm signed-byte-p-of-nth
  (implies (and (all-signed-byte-p size lst)
                (<= 0 n)
                (< n (len lst)))
           (signed-byte-p size (nth n lst)))
  :hints (("Goal" :in-theory (e/d (all-signed-byte-p nth) ()))))

;add to forall
(defthm all-signed-byte-p-of-nil
  (equal (all-signed-byte-p n nil)
         t)
  :hints (("Goal" :in-theory (enable all-signed-byte-p))))

(defthm all-signed-byte-p-of-update-nth
  (implies (and (signed-byte-p m val)
                (<= n (len lst))
                (all-signed-byte-p m lst))
           (all-signed-byte-p m (update-nth n val lst)))
  :hints (("Goal" :in-theory (enable update-nth all-signed-byte-p))))
