

(funcdef logical_or (a b) (block (return (logior1 a b))))(funcdef logical_and (a b) (block (return (logand1 a b))))(funcdef logical_not (a) (block (return (lognot1 a))))
