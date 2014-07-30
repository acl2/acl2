;; Silly file to trick cert.pl into including the right books.

(in-package "ACL2")

#||
(include-book "misc/file-io" :dir :system)
(include-book "misc/rtl-untranslate" :dir :system)
(include-book "misc/symbol-btree" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)
(include-book "rtl/rel4/lib/rtl" :dir :system)
(include-book "rtl/rel4/lib/rtlarr" :dir :system)
(include-book "rtl/rel4/lib/simplify-model-helpers" :dir :system)
(include-book "rtl/rel4/lib/top" :dir :system))
(include-book "rtl/rel4/lib/util" :dir :system)
(include-book "rtl/rel4/support/bvecp-helpers" :dir :system)
||#
