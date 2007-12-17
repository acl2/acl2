(in-package "ACL2")

(local (defun %%sub1-induction (n)
              (if (zp n)
                  n (%%sub1-induction (1- n)))))

(local (defun %%and-tree-fn (args len)
              (declare (xargs :mode :program))
              (if (< len 20)
                  (cons 'and args)
                  (let* ((len2 (floor len 2)))
                        (list 'and
                              (%%and-tree-fn (take len2 args) len2)
                              (%%and-tree-fn (nthcdr len2 args)
                                             (- len len2)))))))

(local (defmacro %%and-tree (&rest args)
                 (%%and-tree-fn args (length args))))

(local (include-book "bvecp-raw"))

(local (include-book "../../../../../rtl/rel4/lib/top"))

(local (include-book "../../../../../rtl/rel4/lib/simplify-model-helpers"))

(include-book "model-raw")

(include-book "model")

(local (table user-defined-functions-table
              nil nil :clear))

(local (disable-forcing))

(local (deftheory theory-0 (theory 'minimal-theory)))

(local (defmacro %%p0-equalities nil
                 '(%%and-tree (equal (out1$ n $path)
                                     (foo$raw::out1$ n $path))
                              (equal (out2$ n $path)
                                     (foo$raw::out2$ n $path)))))

(local (defun %%p0-aux (n $path)
              (declare (xargs :normalize nil))
              (%%p0-equalities)))

(local (defun-sk %%p0 (n)
                 (forall ($path) (%%p0-aux n $path))))

(local (defthm %%p0-implies-%%p0-aux
               (implies (%%p0 n) (%%p0-aux n $path))))

(local (encapsulate
            nil
            (local (defthm %%p0-property-lemma
                           (implies (%%p0-aux n $path)
                                    (%%p0-equalities))
                           :rule-classes nil
                           :instructions ((:dv 1)
                                          (:expand nil)
                                          :top
                                          (:generalize ((%%p0-equalities) eqs))
                                          :s)))
            (defthm %%p0-property
                    (implies (%%p0 n) (%%p0-equalities))
                    :instructions ((:use %%p0-property-lemma)
                                   (:generalize ((%%p0-equalities) eqs))
                                   :prove))))

(local
     (deftheory %%p0-implies-f-is-%f-theory
                (union-theories (set-difference-theories (current-theory :here)
                                                         (current-theory '%%p0))
                                (theory 'minimal-theory))))

(local
     (encapsulate
          nil
          (local (in-theory (disable %%p0-property)))
          (local (defthm out2$-is-out2$-base
                         (implies (zp n)
                                  (equal (out2$ n $path)
                                         (foo$raw::out2$ n $path)))
                         :hints (("Goal" :expand ((out2$ n $path)
                                                  (foo$raw::out2$ n $path))))))
          (local (defthm out1$-is-out1$-base
                         (implies (zp n)
                                  (equal (out1$ n $path)
                                         (foo$raw::out1$ n $path)))
                         :hints (("Goal" :expand ((out1$ n $path)
                                                  (foo$raw::out1$ n $path))))))
          (defthm %%p0-base (implies (zp n) (%%p0 n))
                  :instructions (:promote :x-dumb (:s :normalize nil)))))

(local
     (encapsulate
          nil
          (local (in-theory (disable %%p0 %%p0-base)))
          (local (deflabel %%induction-start))
          (local (defthm out2$-is-out2$-induction_step
                         (implies (and (not (zp n)) (%%p0 (1- n)))
                                  (equal (out2$ n $path)
                                         (foo$raw::out2$ n $path)))
                         :instructions (:promote (:dv 1)
                                                 :x-dumb
                                                 :nx :x-dumb
                                                 :top (:s :normalize nil
                                                          :backchain-limit 1000
                                                          :expand :lambdas
                                                          :repeat 4))))
          (local (defthm out1$-is-out1$-induction_step
                         (implies (and (not (zp n)) (%%p0 (1- n)))
                                  (equal (out1$ n $path)
                                         (foo$raw::out1$ n $path)))
                         :instructions (:promote (:dv 1)
                                                 :x-dumb
                                                 :nx :x-dumb
                                                 :top (:s :normalize nil
                                                          :backchain-limit 1000
                                                          :expand :lambdas
                                                          :repeat 4))))
          (defthm %%p0-induction_step
                  (implies (and (not (zp n)) (%%p0 (1- n)))
                           (%%p0 n))
                  :instructions (:promote :x-dumb (:s :normalize nil)))))

(local
 (defthm
  %%p0-holds (%%p0 n)
  :hints
  (("Goal" :induct (%%sub1-induction n)
           :do-not '(preprocess)
           :in-theory (union-theories '(%%p0-base %%p0-induction_step
                                                  (:induction %%sub1-induction))
                                      (theory 'minimal-theory))))))

(ENCAPSULATE
 (
 )

 (local (in-theory (union-theories '(%%p0-holds)
                                   (theory '%%p0-implies-f-is-%f-theory))))

 (defthm out2$-is-out2$
         (equal (out2$ n $path)
                (foo$raw::out2$ n $path))
         :hints (("Goal" :do-not '(preprocess))))

 (defthm out1$-is-out1$
         (equal (out1$ n $path)
                (foo$raw::out1$ n $path))
         :hints (("Goal" :do-not '(preprocess))))

)

(deftheory %-removal-theory
           (union-theories '(out1$-is-out1$ out2$-is-out2$)
                           (theory 'minimal-theory)))

