(setq domainfile "mprime-domain.pddl")
(setq problemfile "mprime-problem.pddl")
(setq outputfile "mprime")

(setq plan '((feast 'aesthetics 'shrimp 'scallion 'quebec 'bosnia)
(feast 'aesthetics 'scallion 'muffin 'surrey 'quebec)
(overcome 'hangover 'aesthetics 'muffin 'mars 'vulcan)
(feast 'aesthetics 'muffin 'arugula 'oregon 'kentucky)
(feast 'aesthetics 'arugula 'scallop 'oregon 'kentucky)
(succumb 'hangover 'aesthetics 'scallop 'mars 'vulcan)
(feast 'aesthetics 'scallop 'grapefruit 'bosnia 'oregon)
(overcome 'sciatica 'aesthetics 'grapefruit 'mars 'vulcan)
(drink 'cherry 'grapefruit 'kentucky 'oregon 'bosnia 'surrey 'quebec)
(feast 'aesthetics 'grapefruit 'wurst 'surrey 'quebec)
(succumb 'sciatica 'aesthetics 'wurst 'mars 'vulcan)))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

;Real time: 0.088123 sec.
;Run time: 0.087967 sec.
;Space: 16793288 Bytes
;GC: 18, GC time: 0.024597 sec.
;"compiling..." Checking mprime (/home/alasdair/Documents/Sep_PDDL/New Code/Equality/mprime.agda).
;Real time: 44.589264 sec.
;Run time: 1.03E-4 sec.
;Space: 360 Bytes
