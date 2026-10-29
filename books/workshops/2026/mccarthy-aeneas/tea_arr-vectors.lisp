(in-package "ACL2")
(include-book "rust_tea_arr")
;; Same known-answer vectors, array API. encrypt returns (ok (list y z)).
(assert-event (equal (rust-tea-arr-encrypt 33 (list 0 0) (list 0 0 0 0))
                     (ok (list #x41ea3a0a #x94baa940))))
(assert-event (equal (rust-tea-arr-encrypt 33 (list #x12345678 #x9abcdef0) (list 1 2 3 4))
                     (ok (list #xf7995c6a #x182250b1))))
(assert-event
 (equal (b* (((ok c) (rust-tea-arr-encrypt 33 (list #x12345678 #x9abcdef0) (list 1 2 3 4))))
          (rust-tea-arr-decrypt 33 c (list 1 2 3 4)))
        (ok (list #x12345678 #x9abcdef0))))
