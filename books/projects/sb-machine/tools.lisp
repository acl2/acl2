; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "sb")

(defalist ghost-state
  :key-type symbolp
  :true-listp t

  ///
  (defrule put-assoc-ghost-state
    (implies (and (ghost-state-p ghost-state)
                  (symbolp var))
             (ghost-state-p (put-assoc var val ghost-state)))
    :enable put-assoc)
  (defrule assoc-ghost-state
    (implies (and (ghost-state-p ghost-state)
                  (assoc loc ghost-state))
             (and (consp (assoc loc ghost-state))
                  (symbolp (car (assoc loc ghost-state)))))
    :enable assoc)
  (defrule ghost-state-eqlable-alistp
    (implies (ghost-state-p ghost-state)
             (eqlable-alistp ghost-state))))

(define store-buffer-plus-memory-sb
  ((true-sb sb-p)
   (mem memory-p)
   (match-sb sb-p))
  :returns (match-sb? booleanp)
  (b* (((when (endp match-sb)) t)
       ((sb-element match-sb-first) (car match-sb))
       ((when (endp true-sb))
        (and (equal (cdr (assoc match-sb-first.addr mem)) match-sb-first.val)
             (store-buffer-plus-memory-sb true-sb mem (cdr match-sb))))
       (true-sb-first (car true-sb)))
      (and (equal true-sb-first match-sb-first)
           (store-buffer-plus-memory-sb (cdr true-sb) mem (cdr match-sb)))))

(defun sb-deq-ind (x)
  (if (consp x)
      (sb-deq-ind (sb-deq x))
    x))

;; not true. dang
;; (defrule sb-deq-store-buffer-plus-memory-sb
;;   (implies (and (sb-p true-sb)
;;                 (consp true-sb)
;;                 (memory-p mem)
;;                 (sb-p match-sb))
;;            (equal (store-buffer-plus-memory-sb
;;                    (sb-deq true-sb)
;;                    (put-assoc-equal
;;                     (sb-element->addr (sb-next true-sb))
;;                     (sb-element->val (sb-next true-sb))
;;                     mem)
;;                    match-sb)
;;                   (store-buffer-plus-memory-sb true-sb mem match-sb)))
;;   :enable (store-buffer-plus-memory-sb sb-deq sb-next)
;;   :induct (sb-deq-ind true-sb)
;;   :otf-flg t)

(define store-buffer-plus-memory
  ((m machine-p)
   (i (and (natp i) (< i (num-procs m))))
   (match-sb sb-p))
  :returns (match-sb? booleanp)
  (b* (((machine m) m)
       ((proc proc) (nth i m.procs)))
      (store-buffer-plus-memory-sb proc.sb m.mem match-sb)))

(defrule write-sb-store-buffer-plus-memory
  (implies (and (machine-p m)
                (natp i)
                (< i (num-procs m))
                (sb-p match-sb)
                (sb-element-p sb-element)
                (symbolp addr)
                (integerp val))
           (equal
            (store-buffer-plus-memory
             (write-sb m i val addr)
             i
             (cons sb-element match-sb))
            (and (equal val (sb-element->val sb-element))
                 (equal addr (sb-element->addr sb-element))
                 (store-buffer-plus-memory m i match-sb))))
  :enable (store-buffer-plus-memory
           store-buffer-plus-memory-sb
           write-sb
           sb-enq))

(defrule phase-machine-store-buffer-plus-memory
  (implies (and (machine-p m)
                (natp i)
                (< i (num-procs m))
                (natp j)
                (< j (num-procs m))
                (sb-p match-sb))
           (equal
            (store-buffer-plus-memory (phase-machine m j nph npc ntd)
                                      i match-sb)
            (store-buffer-plus-memory m i match-sb)))
  :enable (store-buffer-plus-memory
           phase-machine))

;; (defrule flush-sb-store-buffer-plus-memory
;;   (implies (and (machine-p m)
;;                 (natp i)
;;                 (< i (num-procs m))
;;                 (sb-p match-sb))
;;            (equal (store-buffer-plus-memory (flush-sb m i)
;;                                             i match-sb)
;;                   (store-buffer-plus-memory m i match-sb)))
;;   :enable (store-buffer-plus-memory
;;            flush-sb))
