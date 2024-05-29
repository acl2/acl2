; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-c-preprocessor)


(include-book "std/testing/must-eval-to" :dir :system)
(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

(include-book "../preprocess-file")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bytes-to-string
  ((bytes byte-listp))
  :returns (str stringp)
  (coerce (bytes-to-characters bytes) 'string)
  :prepwork
  ((define bytes-to-characters
     ((bytes byte-listp))
     :returns (chars character-listp
                     :hints (("Goal" :in-theory (enable character-listp)
                                     :induct (bytes-to-characters bytes))))
     (if (endp bytes)
         nil
       (cons (code-char (first bytes))
             (bytes-to-characters (rest bytes))))
     :guard-hints (("Goal" :in-theory (enable byte-listp
                                              bytep
                                              unsigned-byte-p))))))


(defmacro preprocess-file-to-string (filepath &rest args)
  `(b* (((er (cons out bytes))
         (preprocess-file ,filepath ,@args)))
     (value (cons out
                  (bytes-to-string (filedata->unwrap bytes))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed
  (acl2::must-eval-to
    (preprocess-file-to-string (filepath "stdbool.c"))
    (cons nil "int main(void) {
  return (int)0;
}
")))

(acl2::must-succeed
  (acl2::must-eval-to-t
    (b* (((er (cons out str))
          (preprocess-file-to-string (filepath "stdbool.c") :out "stdbool.c.preprocessed")))
      (value (and (stringp out)
                  (equal str "int main(void) {
  return (int)0;
}
"))))))

(acl2::must-succeed
  (acl2::must-eval-to
    ;; Idempotence
    (preprocess-file-to-string (filepath "stdbool.c.preprocessed"))
    (cons nil "int main(void) {
  return (int)0;
}
")))

(acl2::must-succeed
  (acl2::must-eval-to
    (preprocess-file-to-string (filepath "stdbool.c") :out "stdbool.c.preprocessed" :save nil)
    (cons nil "int main(void) {
  return (int)0;
}
")))

(acl2::must-fail
  (preprocess-file (filepath "nonexistent-file.c")))

(acl2::must-succeed
  (preprocess-file-to-string (filepath "stdint.c")))

(acl2::must-succeed
  (preprocess-files
    (mergesort (list (filepath "stdbool.c")
                     (filepath "stdint.c")))))

(acl2::must-succeed
  (acl2::must-eval-to
    (preprocess-files nil)
    (fileset nil)))
