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
