include ../../../../../Makefile-generic
ACL2 = ../../../../../../saved_acl2

# From make dependencies:

coe-fld.cert: coe-fld.lisp
coe-fld.cert: coe-fld.acl2

fucongruencias-producto.cert: fucongruencias-producto.lisp
fucongruencias-producto.cert: fuproducto.cert
fucongruencias-producto.cert: fucongruencias-producto.acl2

fucongruencias-suma.cert: fucongruencias-suma.lisp
fucongruencias-suma.cert: fusuma.cert
fucongruencias-suma.cert: fucongruencias-suma.acl2

fuforma-normal.cert: fuforma-normal.lisp
fuforma-normal.cert: fupolinomio.cert
fuforma-normal.cert: fuforma-normal.acl2

fumonomio.cert: fumonomio.lisp
fumonomio.cert: coe-fld.cert
fumonomio.cert: futermino.cert
fumonomio.cert: fumonomio.acl2

fuopuesto.cert: fuopuesto.lisp
fuopuesto.cert: fucongruencias-suma.cert
fuopuesto.cert: fuopuesto.acl2

fupolinomio-normalizado.cert: fupolinomio-normalizado.lisp
fupolinomio-normalizado.cert: fucongruencias-producto.cert
fupolinomio-normalizado.cert: fupolinomio-normalizado.acl2

fupolinomio.cert: fupolinomio.lisp
fupolinomio.cert: fumonomio.cert
fupolinomio.cert: fupolinomio.acl2

fuproducto.cert: fuproducto.lisp
fuproducto.cert: fuopuesto.cert
fuproducto.cert: fuproducto.acl2

fuquot-rem.cert: fuquot-rem.lisp
fuquot-rem.cert: fupolinomio-normalizado.cert
fuquot-rem.cert: fuquot-rem.acl2

fusuma.cert: fusuma.lisp
fusuma.cert: fuforma-normal.cert
fusuma.cert: fusuma.acl2

futermino.cert: futermino.lisp
futermino.cert: futermino.acl2
