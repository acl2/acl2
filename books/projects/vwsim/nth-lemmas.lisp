; nth-lemmas.lisp                             Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")

(defmacro !nth (key val l)
 `(update-nth ,key ,val ,l))

(add-macro-fn !nth update-nth)  ;; UPDATE-NTH shown as !NTH

(defthm nth-!nth
  ;; Already known
  (equal (nth i (!nth i v l))
         v))

(defthm !nth-nth
  (implies (or (and (natp ma)
                    (< ma (len l)))
               (< (nfix ma) (len l)))
           (equal (!nth ma (nth ma l) l)
                  l)))

(defthm !nth-!nth-same-address
  (implies (equal a1 a2)
           (equal (!nth a1 v (!nth a2 w st))
                  (!nth a1 v st))))

(defthm !nth-!nth-different-addresses
  (implies (not (equal (nfix a1) (nfix a2)))
           (equal (!nth a1 v1 (!nth a2 v2 st))
                  (!nth a2 v2 (!nth a1 v1 st)))))

(defthm len-!nth
  (implies (natp i)
           (equal (len (!nth i v l))
                  (if (< i (len l))
                      (len l)
                    (1+ i)))))

(deftheory nth-theory-defuns
  '(nth update-nth !nth))

(deftheory nth-theory-lemmas
  '(nth-!nth nth-update-nth
             !nth-nth
             !nth-!nth-same-address
             !nth-!nth-different-addresses
             len-!nth))

(in-theory (disable nth-theory-defuns nth-theory-lemmas))
