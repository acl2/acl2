(in-package "ACL2")

(include-book "centaur/misc/tshell" :dir :system)
(include-book "kestrel/strings-light/split-string" :dir :system)
(include-book "kestrel/strings-light/strip-suffix-from-strings" :dir :system)

;; (defun substring-before-first (string char)
;;   (declare (xargs :guard (and (characterp char)
;;                               (stringp string))))
;;   (mv-let (foundp string-before string-after)
;;     (split-string string char)
;;     (declare (ignore string-after))
;;     (if (not foundp)
;;         (er hard? 'substring-before-first "Failed to find a ~x0 in ~s1." char string)
;;       string-before)))

;; (defund substrings-before-first (strings char)
;;   (declare (xargs :guard (and (characterp char)
;;                               (string-listp strings))))
;;   (if (endp strings)
;;       nil
;;     (cons (substring-before-first (first strings) char)
;;           (substrings-before-first (rest strings) char))))

;; Finds all the books in the current directory tree that have .cert.out files indicating that a certification failure occurred.
;; Returns a list of book-paths (without .lisp extensions).
(defun find-failed-books ()
  (prog2$
   (tshell-start)
   (mv-let (status lines)
     (tshell-call "find . -name \"*.cert.out\" -exec grep -Hl 'ACL2 Error \\[.*] in (CERTIFY-BOOK' {} \\;" :print nil)
     (if (not (= 0 status))
         (er hard? 'find-failed-books "Error (~x0) finding failed books.")
       ;(substrings-before-first lines #\:)
       (strip-suffix-from-strings ".cert.out" lines)))))
