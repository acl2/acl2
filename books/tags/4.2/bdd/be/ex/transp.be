@BE1

@invar
 (A B C D)

@sub
SUB1X = 
(NOT (OR A B))
SUB1Y = 
(NOT (OR C D))

@out
O1 = 
(AND SUB1X SUB1Y) 
O2 = 
(NOT (OR SUB1X SUB1Y)) 
@end


@BE2

@invar
 (A B C D)

@out
O1 = 
(AND (NOT A) (NOT B) (NOT C) (NOT D))
O2 = 
(AND (OR A B) (OR C D))

@end
