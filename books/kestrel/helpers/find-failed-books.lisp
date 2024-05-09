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
   (mv-let (status failed-lines)
     (tshell-call "find . -name \"*.cert.out\" -exec grep -Hl 'ACL2 Error \\[.*] in (CERTIFY-BOOK' {} \\;" :print nil)
     (if (not (= 0 status))
         (er hard? 'find-failed-books "Error (~x0) finding failed books.")
       ;; Attempt to identify interrupted books (we will avoid looking for repairs for them):
       (mv-let (status interrupted-lines)
         ;; TODO: This may not find interrupts of the proof checker (try interrupting books/projects/apply-model-2/apply-prim)?:
         (tshell-call "find . -name \"*.cert.out\" -exec grep -Hl 'cause an explicit interrupt' {} \\;" :print nil)
         (if (not (= 0 status))
             (er hard? 'find-failed-books "Error (~x0) finding interrupted books.")
           (let ((failed-books (strip-suffix-from-strings ".cert.out" failed-lines))
                 (interrupted-books (strip-suffix-from-strings ".cert.out" interrupted-lines)))
             (progn$
               (cw "Found ~x0 failed books: ~X12~%" (len failed-books) failed-books nil)
               (cw "Found ~x0 interrupted books: ~X12~%" (len interrupted-books) interrupted-books nil)
               ;;(substrings-before-first lines #\:)
               (set-difference-equal failed-books interrupted-books)))))))))
