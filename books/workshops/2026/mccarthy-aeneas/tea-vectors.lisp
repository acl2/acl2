; Executable known-answer vectors for the extracted TEA (rust_tea.lisp),
; cross-checked against the Kestrel TEA spec's own test vectors.
(in-package "ACL2")
(include-book "rust_tea")
(assert-event (equal (rust-tea-encrypt 33 0 0 0 0 0 0) (ok (cons #x41ea3a0a #x94baa940))))
(assert-event (equal (rust-tea-encrypt 33 #x12345678 #x9abcdef0 1 2 3 4)
                     (ok (cons #xf7995c6a #x182250b1))))
(assert-event
 (equal (b* (((ok c) (rust-tea-encrypt 33 #x12345678 #x9abcdef0 1 2 3 4)))
          (rust-tea-decrypt 33 (car c) (cdr c) 1 2 3 4))
        (ok (cons #x12345678 #x9abcdef0))))
