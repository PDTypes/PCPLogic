(setq domainfile "blocksworld-domain.pddl")
(setq problemfile "blocksworld-problem.pddl")
(setq outputfile "blocksworld")

; plan length 10
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

#||
Real time: 0.017343 sec.
Run time: 0.017103 sec.
Space: 2358736 Bytes
GC: 1, GC time: 0.003505 sec.
"compiling..." Checking blocksworld (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Blockworld/blocksworld.agda).

Real time: 9.80057 sec.
Run time: 8.2E-5 sec.
Space: 376 Bytes
||#


