; Low level memory management utilities
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "mem-logic")
(include-book "tools/include-raw" :dir :system)

(defttag :mem)
(include-raw "mem-raw.lsp")


#||

(include-book
 "mem")

:doc memory

(mem-get-egc state)
(mem-set-egc t)
(mem-get-egc state)
(mem-set-egc nil)
(mem-get-egc state)

(mem-get-free-bytes state)
(mem-get-used-bytes state)

(defun f ()
  (append (make-list 1000)
          (pairlis$
           (make-list 1000 :initial-element :a)
           (make-list 1000 :initial-element :b))))

(defconst *a* (f))

(mem-get-free-bytes state)
(mem-get-used-bytes state)


(mem-get-gc-threshold state)
(mem-set-gc-threshold 10000) ;; Very tiny!
(mem-get-gc-threshold state)

(mem-get-used-bytes state)
(mem-get-free-bytes state)

(mem-use-gc-threshold)

(mem-get-used-bytes state)
(mem-get-free-bytes state)
(mem-get-gc-threshold state)


(mem-set-gc-threshold (expt 2 20)) ;; 1 MB


(defun chatty-gc-hook (state)
  (declare (xargs :stobjs state))
  (progn$
   (cw "~%; Chatty GC hook invoked!~%")
   state))

(defattach mem-gc-hook chatty-gc-hook)

;; You can just force GCs to see the chatty hook running on CCL.  Note how
;; it runs slightly after the GC.

(gc$)
(gc$)


||#