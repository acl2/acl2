
(in-package "ACL2")

(include-book "build/ifdef" :dir :system)

(ifdef "A0"
  (ifdef-define "B0")
  (ifdef-define "B1")
  (ifdef-define "B2")
  (ifdef-define! "C0")
  (ifdef-define! "C1")
  (ifdef-define! "C2")
  :endif)

(ifdef "A1"
  (ifdef-undefine "B0")
  (ifdef-undefine! "B2")
  (ifdef-undefine "B3")
  (ifdef-undefine "C0")
  (ifdef-undefine! "C2")
  (ifdef-undefine! "C3")
  :endif)

(ifdef "B0"
  (include-book "test1b0")
  :endif)

(ifdef "C0"
  (include-book "test1c0")
  :endif)

(ifndef "B0"
  (include-book "test1nb0")
  :endif)

(ifndef "C0"
  (include-book "test1nc0")
  :endif)

(ifdef "B1"
  (include-book "test1b1")
  :endif)

(ifdef "C1"
  (include-book "test1c1")
  :endif)

(ifndef "B1"
  (include-book "test1nb1")
  :endif)

(ifndef "C1"
  (include-book "test1nc1")
  :endif)

(ifdef "B2"
  (include-book "test1b2")
  :endif)

(ifdef "C2"
  (include-book "test1c2")
  :endif)

(ifndef "B2"
  (include-book "test1nb2")
  :endif)

(ifndef "C2"
  (include-book "test1nc2")
  :endif)



(ifdef "B3"
  (include-book "test1b3")
  :endif)

(ifdef "C3"
  (include-book "test1c3")
  :endif)

(ifndef "B3"
  (include-book "test1nb3")
  :endif)

(ifndef "C3"
  (include-book "test1nc3")
  :endif)


