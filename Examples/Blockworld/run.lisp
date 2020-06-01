(setq domainfile "blocksworld-domain.pddl")
(setq problemfile "blocksworld-problem.pddl")
(setq outputfile "blocksworld")

(setq plan '((pickup_from_table 'e)
(putdown_on_stack 'e 'f1)
(pickup_from_table 'd)
(putdown_on_stack 'd 'e)
(pickup_from_table 'c)
(putdown_on_stack 'c 'd)
(pickup_from_table 'b)
(putdown_on_stack 'b 'c)
(pickup_from_table 'a)
(putdown_on_stack 'a 'b)))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

;Real time: 0.030017 sec.
;Run time: 0.029494 sec.
;Space: 2251968 Bytes
;GC: 2, GC time: 0.003461 sec.
;"compiling..."
;Real time: 10.33406 sec.
;Run time: 1.03E-4 sec.
;Space: 376 Bytes
