---
date: 2022-01-07T08:00:00Z
title: 'Function THREAD-NAME, THREAD-NATIVE-THREAD'
weight: 2
---

#### Syntax:

**thread-name** thread => name\
**thread-native-thread** thread => native-thread

#### Arguments and values:

*thread* -> an instance of class [**thread**](../class-thread).\
*name* -> a
[string](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_s.htm#string)
or
[nil](http://www.lispworks.com/documentation/HyperSpec/Body/a_nil.htm#nil)\
*native-thread* -> a host thread instance.

#### Description:

These accessors return the public slots of class [**thread**](../class-thread).

#### Exceptional situations:

None.
