门票 :- NP\NP : (lambda $0:e (ticket:<e,t> $0))
的 :- NP/NP\NP : (lambda $2:sc (lambda $1:<e,t> (lambda $0:e (and:<t*,t> ($1 $0) (loc:<e,<lo,t>> $0 $2)))))
多少钱 :- S\NP : (lambda $0:<e,t> (price:<<e,t>,i> $0))
