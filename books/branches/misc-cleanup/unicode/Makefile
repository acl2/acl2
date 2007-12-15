include ../Makefile-generic
ACL2 = ../../saved_acl2

BASICS = app append base10-digit-charp coerce consless-listp combine \
         explode-atom explode-nonnegative-integer flatten \
         intern-in-package-of-symbol list-fix nat-listp nthcdr \
         partition repeat revappend reverse sign-byte signed-byte-listp \
         string-append sum-list take unsigned-byte-listp z-listp

IO = update-state open-input-channels open-input-channel close-input-channel \
     read-byte read-char peek-char read-object \
     file-measure read-file-bytes read-file-characters read-ints \
     nthcdr-bytes take-bytes

UNICODE = uchar utf8-table35 utf8-table36 utf8-encode utf8-decode read-utf8


BOOKS = $(BASICS) $(IO) $(UNICODE)


app.cert: app.lisp
app.cert: list-fix.cert
app.cert: take.cert
app.cert: nthcdr.cert
# app.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

append.cert: append.lisp
# append.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

base10-digit-charp.cert: base10-digit-charp.lisp

coerce.cert: coerce.lisp

consless-listp.cert: consless-listp.lisp
consless-listp.cert: app.cert

combine.cert: combine.lisp
combine.cert: sign-byte.cert
combine.cert: unsigned-byte-listp.cert
combine.cert: signed-byte-listp.cert

explode-atom.cert: explode-atom.lisp
explode-atom.cert: base10-digit-charp.cert
explode-atom.cert: explode-nonnegative-integer.cert

explode-nonnegative-integer.cert: explode-nonnegative-integer.lisp
explode-nonnegative-integer.cert: revappend.cert
explode-nonnegative-integer.cert: base10-digit-charp.cert
# explode-nonnegative-integer.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

flatten.cert: flatten.lisp
flatten.cert: app.cert
flatten.cert: consless-listp.cert

intern-in-package-of-symbol.cert: intern-in-package-of-symbol.lisp

list-fix.cert: list-fix.lisp

nat-listp.cert: nat-listp.lisp
nat-listp.cert: app.cert

nthcdr.cert: nthcdr.lisp
# nthcdr.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

partition.cert: partition.lisp
partition.cert: flatten.cert
partition.cert: sum-list.cert
partition.cert: z-listp.cert
partition.cert: nthcdr.cert
# partition.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert

repeat.cert: repeat.lisp
repeat.cert: take.cert

revappend.cert: revappend.lisp
# revappend.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

reverse.cert: reverse.lisp
reverse.cert: revappend.cert
reverse.cert: coerce.cert

sign-byte.cert: sign-byte.lisp

signed-byte-listp.cert: signed-byte-listp.lisp
signed-byte-listp.cert: unsigned-byte-listp.cert
# signed-byte-listp.cert: $(ACL2_SYSTEM_BOOKS)/ihs/logops-lemmas.cert
# signed-byte-listp.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# signed-byte-listp.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

string-append.cert: string-append.lisp
string-append.cert: append.cert
string-append.cert: coerce.cert

sum-list.cert: sum-list.lisp
sum-list.cert: nat-listp.cert

take.cert: take.lisp
# take.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

unsigned-byte-listp.cert: unsigned-byte-listp.lisp
unsigned-byte-listp.cert: take.cert
unsigned-byte-listp.cert: nat-listp.cert
unsigned-byte-listp.cert: repeat.cert
# unsigned-byte-listp.cert: $(ACL2_SYSTEM_BOOKS)/ihs/logops-lemmas.cert
# unsigned-byte-listp.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
# unsigned-byte-listp.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/floor-mod/floor-mod.cert

z-listp.cert: z-listp.lisp
z-listp.cert: app.cert

update-state.cert: update-state.lisp

open-input-channels.cert: open-input-channels.lisp

open-input-channel.cert: open-input-channel.lisp
open-input-channel.cert: update-state.cert
open-input-channel.cert: open-input-channels.cert
open-input-channel.cert: explode-nonnegative-integer.cert
open-input-channel.cert: intern-in-package-of-symbol.cert
open-input-channel.cert: coerce.cert
# open-input-channel.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

close-input-channel.cert: close-input-channel.lisp
close-input-channel.cert: update-state.cert
close-input-channel.cert: open-input-channels.cert

read-byte.cert: read-byte.lisp
read-byte.cert: update-state.cert
read-byte.cert: open-input-channels.cert
read-byte.cert: unsigned-byte-listp.cert
read-byte.cert: signed-byte-listp.cert

read-char.cert: read-char.lisp
read-char.cert: update-state.cert
read-char.cert: open-input-channels.cert

peek-char.cert: peek-char.lisp
peek-char.cert: update-state.cert
peek-char.cert: open-input-channels.cert

read-object.cert: read-object.lisp
read-object.cert: update-state.cert
read-object.cert: open-input-channels.cert

file-measure.cert: file-measure.lisp
file-measure.cert: update-state.cert
file-measure.cert: open-input-channels.cert

read-file-bytes.cert: read-file-bytes.lisp
read-file-bytes.cert: file-measure.cert
read-file-bytes.cert: unsigned-byte-listp.cert
read-file-bytes.cert: open-input-channel.cert
read-file-bytes.cert: close-input-channel.cert
read-file-bytes.cert: read-byte.cert

read-file-characters.cert: read-file-characters.lisp
read-file-characters.cert: file-measure.cert
read-file-characters.cert: open-input-channel.cert
read-file-characters.cert: read-char.cert
read-file-characters.cert: close-input-channel.cert

read-ints.cert: read-ints.lisp
read-ints.cert: read-byte.cert
read-ints.cert: unsigned-byte-listp.cert
read-ints.cert: signed-byte-listp.cert
read-ints.cert: sign-byte.cert
read-ints.cert: combine.cert
# read-ints.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

nthcdr-bytes.cert: nthcdr-bytes.lisp
nthcdr-bytes.cert: read-byte.cert
nthcdr-bytes.cert: read-file-bytes.cert

take-bytes.cert: take-bytes.lisp
take-bytes.cert: read-byte.cert
take-bytes.cert: read-file-bytes.cert
take-bytes.cert: nthcdr-bytes.cert

uchar.cert: uchar.lisp

utf8-table35.cert: utf8-table35.lisp
utf8-table35.cert: uchar.cert
utf8-table35.cert: unsigned-byte-listp.cert
utf8-table35.cert: signed-byte-listp.cert

utf8-table36.cert: utf8-table36.lisp
utf8-table36.cert: uchar.cert
utf8-table36.cert: unsigned-byte-listp.cert
utf8-table36.cert: signed-byte-listp.cert

utf8-encode.cert: utf8-encode.lisp
utf8-encode.cert: utf8-table35.cert
utf8-encode.cert: utf8-table36.cert
utf8-encode.cert: append.cert
utf8-encode.cert: signed-byte-listp.cert

utf8-decode.cert: utf8-decode.lisp
utf8-decode.cert: uchar.cert
utf8-decode.cert: utf8-table35.cert
utf8-decode.cert: utf8-table36.cert
utf8-decode.cert: utf8-encode.cert
utf8-decode.cert: partition.cert
utf8-decode.cert: nthcdr.cert
utf8-decode.cert: signed-byte-listp.cert
utf8-decode.cert: revappend.cert
# utf8-decode.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert

read-utf8.cert: read-utf8.lisp
read-utf8.cert: utf8-decode.cert
read-utf8.cert: take-bytes.cert
read-utf8.cert: open-input-channel.cert
read-utf8.cert: close-input-channel.cert
read-utf8.cert: signed-byte-listp.cert
# read-utf8.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/bind-free/top.cert
