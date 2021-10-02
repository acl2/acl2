; Recognizers for macro args (formals, etc.)
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "quote")

(defund macro-argp (arg)
  (declare (xargs :guard t))
  (or (symbolp arg) ; regular formal or &whole, &optional, etc.
      (and (true-listp arg)
           (or (and (= 1 (len arg)) ; (arg)
                    (symbolp (first arg)))
               (and (= 2 (len arg)) ; (arg 'init)
                    (symbolp (first arg))
                    (myquotep (second arg)))
               (and (= 3 (len arg)) ; (arg 'init supplied-p)
                    (symbolp (first arg))
                    (myquotep (second arg))
                    (symbolp (third arg)))))))

(defund macro-arg-listp (args)
  (declare (xargs :guard t))
  (if (atom args)
      (null args)
    (and (macro-argp (first args))
         (macro-arg-listp (rest args)))))

(defthm macro-argp-of-car
  (implies (macro-arg-listp macro-args)
           (macro-argp (car macro-args)))
  :hints (("Goal" :in-theory (enable macro-arg-listp))))

(defthm macro-arg-listp-of-cdr
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (cdr macro-args)))
  :hints (("Goal" :in-theory (enable macro-arg-listp))))

(defthm macro-arg-listp-forward-to-true-listp
  (implies (macro-arg-listp macro-args)
           (true-listp macro-args))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable macro-arg-listp))))
