
(in-package "ACL2")
(include-book "test1")



(ifdef "B0"
  (include-book "test2b0")
  :endif)

(ifdef "C0"
  (include-book "test2c0")
  :endif)

(ifndef "B0"
  (include-book "test2nb0")
  :endif)

(ifndef "C0"
  (include-book "test2nc0")
  :endif)

(ifdef "B1"
  (include-book "test2b1")
  :endif)

(ifdef "C1"
  (include-book "test2c1")
  :endif)

(ifndef "B1"
  (include-book "test2nb1")
  :endif)

(ifndef "C1"
  (include-book "test2nc1")
  :endif)

(ifdef "B2"
  (include-book "test2b2")
  :endif)

(ifdef "C2"
  (include-book "test2c2")
  :endif)

(ifndef "B2"
  (include-book "test2nb2")
  :endif)

(ifndef "C2"
  (include-book "test2nc2")
  :endif)

(ifdef "B3"
  (include-book "test2b3")
  :endif)

(ifdef "C3"
  (include-book "test2c3")
  :endif)

(ifndef "B3"
  (include-book "test2nb3")
  :endif)

(ifndef "C3"
  (include-book "test2nc3")
  :endif)

