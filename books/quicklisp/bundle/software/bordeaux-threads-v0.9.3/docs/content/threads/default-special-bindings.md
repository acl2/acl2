---
date: 2022-01-07T08:00:00Z
title: 'Variable *DEFAULT-SPECIAL-BINDINGS*'
weight: 5
---

#### Value type:

an
[alist](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_a.htm#alist)
mapping symbol names to forms to evaluate.

#### Initial value:

[nil](http://www.lispworks.com/documentation/HyperSpec/Body/a_nil.htm#nil).

#### Description:

Variables named in this list are locally bound in the new thread,
before it begins executing user code, by calling
[eval](http://www.lispworks.com/documentation/HyperSpec/Body/f_eval.htm#eval)
on its associated form.

This variable may be rebound around calls to [make-thread](../make-thread)
to add/alter default bindings. The effect of mutating this list is
undefined, but earlier forms take precedence over later forms for the
same symbol, so defaults may be overridden by consing to the head of the
list.
  
The bindings in `*default-special-bindings*` are used to determine the
initial bindings of a new thread, and take precedence over a default
list of I/O bindings. The list of initial I/O bindings is not
modifiable by the user and it was chosen to avoid potential
implementation-defined differences in
[with-standard-io-syntax](http://www.lispworks.com/documentation/HyperSpec/Body/m_w_std_.htm#with-standard-io-syntax).

```
*package*                   (find-package :common-lisp-user)
*print-array*               t
*print-base*                10
*print-case*                :upcase
*print-circle*              nil
*print-escape*              t
*print-gensym*              t
*print-length*              nil
*print-level*               nil
*print-lines*               nil
*print-miser-width*         nil
*print-pprint-dispatch*     (copy-pprint-dispatch nil)
*print-pretty*              nil
*print-radix*               nil
*print-readably*            t
*print-right-margin*        nil
*random-state*              (make-random-state t)
*read-base*                 10
*read-default-float-format* 'double-float
*read-eval*                 nil
*read-suppress*             nil
*readtable*                 (copy-readtable nil)
```

#### Examples:

```
;;; Make a thread read integers in base 7.
(let* ((bt2:*default-special-bindings*
        (acons '*read-base* 7
               bt2:*default-special-bindings*))
       (thread (bt2:make-thread (lambda () (read-from-string "10")))))
  (bt2:join-thread thread))
```
=> 7, 2

#### See also:

[**make-thread**](../make-thread)

#### Notes:

The binding code does not check whether a symbol is indeed declared
special or not.
