(setq domainfile "satellite-domain.pddl")
(setq problemfile "satellite-problem.pddl")
(setq outputfile "satellite")

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
