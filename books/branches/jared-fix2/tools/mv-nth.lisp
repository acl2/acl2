
(in-package "ACL2")

(defevaluator eval-for-mv-nth eval-for-mv-nth-list
  ((mv-nth n x)
   (cons a b)))

(defn mv-nth-eval-rec (n x orig)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (case-match
        x
        (('cons a . &) a)
        (('quote (const . &) . &) (list 'quote const))
        (& orig))
    (case-match
      x
      (('cons & d . &) (mv-nth-eval-rec (1- n) d orig))
      (('quote const . &) (list 'quote (ec-call (nth n const))))
      (& orig))))

(defn mv-nth-eval-fn (x)
  (declare (xargs :guard t))
  (case-match
    x
    (('mv-nth ('quote n . &) rst . &)
     (if (natp n)
         (mv-nth-eval-rec n rst x)
       x))
    (& x)))

(defthm eval-for-mv-nth-rec-thm
  (implies (equal (eval-for-mv-nth x a)
                  (mv-nth n (eval-for-mv-nth term a)))
           (equal (eval-for-mv-nth (mv-nth-eval-rec n term x) a)
                  (mv-nth n (eval-for-mv-nth term a))))
  :hints (("Goal" :induct (mv-nth-eval-rec n term x))))

(defthm mv-nth-cons-meta
  (equal (eval-for-mv-nth x a)
         (eval-for-mv-nth (mv-nth-eval-fn x) a))
  :rule-classes ((:meta :trigger-fns (mv-nth))))


(in-theory (disable mv-nth))
