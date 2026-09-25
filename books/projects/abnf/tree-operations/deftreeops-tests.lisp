; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "deftreeops")

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities to build small grammars from strings, one per line.

(defconst *crlf-string* (implode (list #\Return #\Newline)))

(defun lines-with-crlf (lines)
  (if (endp lines)
      nil
    (list* (car lines) '*crlf-string* (lines-with-crlf (cdr lines)))))

(defmacro grammar-from-lines (name &rest lines)
  `(defconst ,name
     (abstract-rulelist
      (parse-grammar
       (string=>nats (str::cat ,@(lines-with-crlf lines)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A rule name defined by duplicate concatenations is rejected.

(grammar-from-lines *grammar-dup*
                    "a = b / b"
                    "b = \"x\"")

(must-fail (deftreeops *grammar-dup* :prefix dup-cst)
           :with-output-off nil)

; Duplicates arising from incremental rules are rejected too.

(grammar-from-lines *grammar-dup-incremental*
                    "a = b / c"
                    "b = \"x\""
                    "c = \"y\""
                    "a =/ c")

(must-fail (deftreeops *grammar-dup-incremental* :prefix dup-incr-cst)
           :with-output-off nil)

; Distinct alternatives are accepted, with the conc? function generated.

(grammar-from-lines *grammar-nodup*
                    "a = b / c"
                    "b = \"x\""
                    "c = \"y\"")

(deftreeops *grammar-nodup* :prefix nodup-cst)

(assert-event (function-symbolp 'nodup-cst-a-conc? (w state)))

; The -match theorems are recorded in the table, under their names.

(assert-event
 (b* ((info (deftreeops-table-lookup '*grammar-nodup* (w state)))
      (event-alist (deftreeops-table-value->event-alist info)))
   (and (assoc-eq 'nodup-cst-a-conc1-match event-alist)
        (assoc-eq 'nodup-cst-a-conc1-rep-match event-alist)
        (assoc-eq 'nodup-cst-a-conc1-rep-elem-match event-alist)
        (assoc-eq 'nodup-cst-b-conc-match event-alist)
        (assoc-eq 'nodup-cst-b-conc-rep-match event-alist)
        (assoc-eq 'nodup-cst-b-conc-rep-elem-match event-alist)
        t)))
