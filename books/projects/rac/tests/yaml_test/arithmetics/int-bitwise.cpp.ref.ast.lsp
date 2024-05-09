

(funcdef bit_and (a b) (block (return (logand a b))))(funcdef bit_or (a b) (block (return (logior a b))))(funcdef bit_not (a) (block (return (lognot a))))(funcdef shift_left (a n) (block (return (ash a n))))(funcdef shift_right (a n) (block (return (ash a (- n)))))(funcdef bit_xor (a b) (block (return (logxor a b))))
