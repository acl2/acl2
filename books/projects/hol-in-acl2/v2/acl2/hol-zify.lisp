(in-package "ZF")

(include-book "v-omega-times-2")

(defun zname (name)
  (declare (xargs :guard (symbolp name)))
  (fix-intern-in-pkg-of-sym (concatenate 'string "Z" (symbol-name name))
                            name))

(defmacro hol-zify (name arity &rest rest)
  `(zify* ,(zname name)
         ,name
         ,arity
         :dom (v-omega*2)
         :ran (v-omega*2)
         ,@rest))

(hol-zify fun-space 2
          :props (zify-prop v$prop v-omega+$prop fun-space$prop))

(hol-zify prod2 2
          :props (zify-prop v$prop v-omega+$prop))

(hol-zify finseqs 1
          :props (zify-prop v$prop v-omega+$prop finseqs$prop))

(defun option (val)
  (declare (xargs :guard (not (equal val 0))))
  (insert :none
          (prod2 (singleton :some)
                 val)))

(hol-zify option 1
          :props (zify-prop v$prop v-omega+$prop))

(defun ki (x y)
  (declare (ignore x)
           (xargs :guard t))
  y)

(hol-zify ki 2
          :props (zify-prop v$prop v-omega+$prop))
