(define-datatype continuation continuation?
	[random-case ...])

(define apply-k
	(lambda (k v)
		(cases continuation k
			[random-case ...])))