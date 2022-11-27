(setq domainfile "satellite-domain.pddl")
(setq problemfile "satellite-problem.pddl")
(setq outputfile "satellite")

;plan length 9
(setq plan '((turn_to 'satellite0 'groundstation2 'phenomenon6)
(switch_on 'instrument0 'satellite0)
(calibrate 'satellite0 'instrument0 'groundstation2)
(turn_to 'satellite0 'phenomenon4 'groundstation2)
(take_image 'satellite0 'phenomenon4 'instrument0 'thermograph0)
(turn_to 'satellite0 'star5 'phenomenon4)
(take_image 'satellite0 'star5 'instrument0 'thermograph0)
(turn_to 'satellite0 'phenomenon6 'star5)
(take_image 'satellite0 'phenomenon6 'instrument0 'thermograph0)))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

#||
Real time: 0.018911 sec.
Run time: 0.018892 sec.
Space: 2944680 Bytes
GC: 1, GC time: 0.003785 sec.
"compiling..." Checking satellite (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Satellite/satellite.agda).

Real time: 11.788809 sec.
Run time: 8.0E-5 sec.
Space: 360 Bytes

||#


