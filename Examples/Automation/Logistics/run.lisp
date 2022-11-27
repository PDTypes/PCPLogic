(setq domainfile "logistics-domain.pddl")
(setq problemfile "logistics-problem.pddl")
(setq outputfile "logistics")

;plan length 24
(setq plan '(
(load-truck 'obj23 'tru2 'pos2)
(load-truck 'obj21 'tru2 'pos2)
(drive-truck 'tru2 'pos2 'apt2 'cit2)
(load-truck 'obj13 'tru1 'pos1)
(load-truck 'obj11 'tru1 'pos1)
(drive-truck 'tru1 'pos1 'apt1 'cit1)
(unload-truck 'obj11 'tru1 'apt1)
(unload-truck 'obj13 'tru1 'apt1)
(unload-truck 'obj21 'tru2 'apt2)
(load-airplane 'obj21 'apn1 'apt2)
(fly-airplane 'apn1 'apt2 'apt1)
(unload-airplane 'obj21 'apn1 'apt1)
(load-truck 'obj21 'tru1 'apt1)
(drive-truck 'tru1 'apt1 'pos1 'cit1)
(unload-truck 'obj21 'tru1 'pos1)
(unload-truck 'obj23 'tru2 'apt2)
(fly-airplane 'apn1 'apt1 'apt2)
(load-airplane 'obj23 'apn1 'apt2)
(fly-airplane 'apn1 'apt2 'apt1)
(unload-airplane 'obj23 'apn1 'apt1)
(drive-truck 'tru1 'pos1 'apt1 'cit1)
(load-truck 'obj23 'tru1 'apt1)
(drive-truck 'tru1 'apt1 'pos1 'cit1)
(unload-truck 'obj23 'tru1 'pos1)))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

#||
Real time: 0.047998 sec.
Run time: 0.046999 sec.
Space: 9414680 Bytes
GC: 5, GC time: 0.016817 sec.
"compiling..." Checking logistics (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Logistics/logistics.agda).

Real time: 18.959225 sec.
Run time: 5.8E-5 sec.
Space: 360 Bytes
||#

