#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "TABLE")

;; The ACL2 table event stuff is really clunky.  I say we manage our
;; data structures in our own way and just use the table events to do
;; atomic updates of those structures.

;; Here are a couple of functions to ease this process.

;; Both of these macros "evaluate" their key argument, so you must
;; quote it if it is a symbol.  

;; Note that keys from the keyword package will cause table events to
;; break.

(defun get-fn (key world)
  (cdr (assoc :data (table-alist key world))))

(defmacro get (key &rest args)
  (if (consp args)
      `(get-fn ,key ,@args)
    `(get-fn ,key world)))

(defmacro set (key event)
  `(make-event
    `(table ,,key :data ,',event :put)))


