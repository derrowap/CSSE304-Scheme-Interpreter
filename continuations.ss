(define-datatype continuation continuation?
	[init-k]
	[rator-k
		(rands (list-of expression?))
		(env environment?)
		(k continuation?)]
	[rands-k
		(proc-value proc-val?)
		(k continuation?)]
	[if-k
		(result expression?)
		(env environment?)
		(k continuation?)]
	[if-else-k
		(result expression?)
		(elseRes expression?)
		(env environment?)
		(k continuation?)]
	[map-recur-k
		(proc-cps procedure?)
		(list-car scheme-value?)
		(k continuation?)]
	[map-apply-k
		(ls list?)
		(k continuation?)])

(define apply-k
	(lambda (k v)
		(cases continuation k
			[init-k ()
				v]
			[rator-k (rands env k)
				(eval-rands rands env (rands-k v k))]
			[rands-k (proc-value k)
				(apply-proc proc-value v k)]
			[if-k (result env k)
				(if v
					(eval-exp result env k))]
			[if-else-k (result elseRes env k)
				(if v
					(eval-exp result env k)
					(eval-exp elseRes env k))]
			[map-recur-k (proc-cps list-car k)
				(proc-cps list-car (map-apply-k v k))]
			[map-apply-k (ls k)
				(apply-k k (cons v ls))])))

(define map-cps
	(lambda (proc-cps ls k)
		(if (null? ls)
			(apply-k k '())
			(map-cps
				proc-cps
				(cdr ls)
				(map-recur-k proc-cps (car ls) k)))))
