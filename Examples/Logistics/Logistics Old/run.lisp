(setq domainfile "logistics-domain.pddl")
(setq problemfile "logistics-problem.pddl")
(setq outputfile "logistics")

(setq plan '((drive 'truck2 'city2 'airport2 'office2)
(drive 'truck1 'city1 'airport1 'office1)
(fly 'airplane1 'airport1 'airport2)
(load 'package1 'truck1 'office1)
(drive 'truck1 'city1 'office1 'airport1)
(unload 'package1 'truck1 'airport1)
(fly 'airplane1 'airport2 'airport1)
(load 'package1 'airplane1 'airport1)
(fly 'airplane1 'airport1 'airport2)
(unload 'package1 'airplane1 'airport2)
(drive 'truck2 'city2 'office2 'airport2)
(load 'package1 'truck2 'airport2)
(drive 'truck2 'city2 'airport2 'office2)
(unload 'package1 'truck2 'office2)))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

;Real time: 0.045203 sec.
;Run time: 0.04427 sec.
;Space: 4315864 Bytes
;GC: 4, GC time: 0.006171 sec.
;"compiling..." Checking logistics (/home/alasdair/Documents/Sep_PDDL/New Code/logistics.agda).
;Real time: 17.581837 sec.
;Run time: 7.5E-5 sec.
;Space: 360 Bytes
