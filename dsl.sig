dsl : Type
bool : Type

seq : Functor

shuffle : dsl
shuffleinv : dsl

retag : dsl

untagL : dsl
untagLinv : dsl

untag : dsl
tagL : dsl

assoc : dsl 
associnv : dsl 

swap : dsl
swapinv : dsl

proj : dsl
projinv : dsl

abortR : dsl
abortRinv : dsl

abortL : dsl
abortLinv : dsl

distL : dsl
distLinv : dsl

distR : dsl 
distRinv : dsl 

wrap : dsl 
wrapinv : dsl 

drop : dsl
dropinv : dsl

cid : dsl

ctrans : dsl -> dsl -> dsl
cplus : dsl -> dsl -> dsl
cseq : dsl -> dsl -> dsl
cstar : dsl -> dsl
cfix : (dsl -> dsl) -> dsl
guard : dsl -> dsl
