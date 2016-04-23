; evaluator for simple expressions.
; Possible starting point for first interpreter assignment.
;                  
; Claude Anderson.  Last modified April, 2014


(load "chez-init.ss") 

(define load-all ; make it easy to reload the files
	(lambda ()
		(load "datatypes.ss")
		(load "parse.ss")
		(load "env.ss")
		(load "interpreter.ss")))

(load-all)


;(load "./CSSE304-Interpreter-Project/chez-init.ss")

;(define load-all ; make it easy to reload the files
;	(lambda ()
;		(load "./CSSE304-Interpreter-Project/datatypes.ss")
;		(load "./CSSE304-Interpreter-Project/parse.ss")
;		(load "./CSSE304-Interpreter-Project/env.ss")
;		(load "./CSSE304-Interpreter-Project/interpreter.ss")))

;(load-all)