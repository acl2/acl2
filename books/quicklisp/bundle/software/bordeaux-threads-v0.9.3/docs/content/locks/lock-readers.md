---
date: 2022-01-07T08:00:00Z
title: Function LOCK-NAME, LOCK-NATIVE-LOCK
weight: 5
---

#### Syntax:

**lock-name** lock => name\
**lock-native-lock** lock => native-lock

#### Arguments and values:

*lock* -> a [lock](../lock) object.\
*name* -> a string or nil.\
*native-lock* -> a native lock object.

#### Description:

**lock-name** returns the lock name, or **nil** of the lock was not given
a name on creation.\
**lock-native-lock** returns the native lock object that is wrapped by `lock`.

#### Exceptional situations:

None.

#### See also:

[**lock**](../lock)

#### Notes:

None.
