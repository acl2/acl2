#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(begin-book t);$ACL2s-Preamble$|#

(in-package "DEFDATA")

(defun my-mv-nth (n v)
  (declare (xargs :guard nil))
  (if (zp n)
    (car v)
    (my-mv-nth (- n 1) (cdr v))))

(defthm my-mv-nth--nil
  (equal (my-mv-nth x nil)
         nil))

(defthm my-mv-nth--reduce1
  (implies (and (syntaxp (integerp n))
                (integerp n)
                (< 0 n))
           (equal (my-mv-nth n v)
                  (my-mv-nth (- n 1) (cdr v)))))

(defthm my-mv-nth--reduce2
  (implies (or (not (integerp n))
               (<= n 0))
           (equal (my-mv-nth n v)
                  (car v))))

; not by default
(defthmd mv-nth--to--my-mv-nth
  (equal (mv-nth x y)
         (my-mv-nth x y)))#|ACL2s-ToDo-Line|#
