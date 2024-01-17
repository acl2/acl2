---
date: 2022-01-07T08:00:00Z
title: 'Function ABNORMAL-EXIT-CONDITION'
weight: 16
---

#### Syntax:

**abnormal-exit-condition** => condition

#### Arguments and values:

*condition* -> a condition object or `:terminated`.

#### Description

Returns the terminating condition of an
[**abnormal-exit**](../abnormal-exit) condition object. If the thread
was terminated by [**destroy-thread**](../destroy-thread) or other
kinds of non-local exits, the keyword `:terminated` is returned.

#### Examples:

```
(let ((thread (bt2:make-thread
               (lambda () (error "This will terminate the thread")))))
  (handler-case
      (bt2:join-thread thread)
    (abnormal-exit (e)
       (abnormal-exit-condition e))))
```
=> `#<SIMPLE-ERROR "This will terminate the thread" {10043E01F3}>`

#### See also:

[**abnormal-exit-condition**](../abnormal-exit-condition),
[**join-thread**](../join-thread)
