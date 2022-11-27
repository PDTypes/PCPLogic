(setq domainfile "blocksworld-domain.pddl")
(setq problemfile "blocksworld-problem.pddl")
(setq outputfile "blocksworld2")

;plan length 20
(setq plan '(
(pickup_from_stack 'e 'g)
(putdown_on_table 'e)
(pickup_from_stack 'g 'b)
(putdown_on_table 'g)
(pickup_from_stack 'b 'a)
(putdown_on_table 'b)
(pickup_from_stack 'a 'h)
(putdown_on_table 'a)
(pickup_from_stack 'h 'c)
(putdown_on_stack 'h 'e)
(pickup_from_stack 'c 'd)
(putdown_on_stack 'c 'h)
(pickup_from_table 'b)
(putdown_on_stack 'b 'c)
(pickup_from_table 'd)
(putdown_on_stack 'd 'b)
(pickup_from_table 'g)
(putdown_on_stack 'g 'd)
(pickup_from_table 'a)
(putdown_on_stack 'a 'g)
))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

#||
Real time: 0.02458 sec.
Run time: 0.024553 sec.
Space: 3870592 Bytes
GC: 2, GC time: 0.006753 sec.
"compiling..." Checking blocksworld2 (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Blocksworld2/blocksworld2.agda).

Real time: 11.647426 sec.
Run time: 8.1E-5 sec.
Space: 376 Bytes

||#

