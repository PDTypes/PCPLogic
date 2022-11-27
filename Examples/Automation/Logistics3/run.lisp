(setq domainfile "logistics-domain.pddl")
(setq problemfile "logistics-problem.pddl")
(setq outputfile "logistics3")

;plan length 74
(setq plan '(
(fly-airplane 'apn1 'apt3 'apt1)
(fly-airplane 'apn1 'apt1 'apt2)
(fly-airplane 'apn1 'apt2 'apt4)
(drive-truck 'tru4 'pos4 'apt4 'cit4)
(drive-truck 'tru3 'pos3 'apt3 'cit3)
(load-truck 'obj23 'tru2 'pos2)
(load-truck 'obj22 'tru2 'pos2)
(drive-truck 'tru2 'pos2 'apt2 'cit2)
(unload-truck 'obj22 'tru2 'apt2)
(fly-airplane 'apn1 'apt4 'apt1)
(fly-airplane 'apn1 'apt1 'apt2)
(fly-airplane 'apn1 'apt2 'apt3)
(load-truck 'obj13 'tru1 'pos1)
(drive-truck 'tru1 'pos1 'apt1 'cit1)
(unload-truck 'obj13 'tru1 'apt1)
(drive-truck 'tru2 'apt2 'pos2 'cit2)
(load-truck 'obj21 'tru2 'pos2)
(drive-truck 'tru3 'apt3 'pos3 'cit3)
(load-truck 'obj33 'tru3 'pos3)
(load-truck 'obj31 'tru3 'pos3)
(drive-truck 'tru4 'apt4 'pos4 'cit4)
(load-truck 'obj42 'tru4 'pos4)
(drive-truck 'tru3 'pos3 'apt3 'cit3)
(unload-truck 'obj31 'tru3 'apt3)
(load-airplane 'obj31 'apn1 'apt3)
(unload-truck 'obj33 'tru3 'apt3)
(load-airplane 'obj33 'apn1 'apt3)
(drive-truck 'tru4 'pos4 'apt4 'cit4)
(unload-truck 'obj42 'tru4 'apt4)
(fly-airplane 'apn1 'apt3 'apt1)
(unload-airplane 'obj33 'apn1 'apt1)
(unload-airplane 'obj31 'apn1 'apt1)
(fly-airplane 'apn1 'apt1 'apt2)
(fly-airplane 'apn1 'apt2 'apt4)
(load-airplane 'obj42 'apn1 'apt4)
(drive-truck 'tru2 'pos2 'apt2 'cit2)
(load-truck 'obj31 'tru1 'apt1)
(drive-truck 'tru1 'apt1 'pos1 'cit1)
(unload-truck 'obj31 'tru1 'pos1)
(fly-airplane 'apn1 'apt4 'apt2)
(unload-airplane 'obj42 'apn1 'apt2)
(fly-airplane 'apn1 'apt2 'apt1)
(load-airplane 'obj13 'apn1 'apt1)
(fly-airplane 'apn1 'apt1 'apt4)
(unload-airplane 'obj13 'apn1 'apt4)
(drive-truck 'tru1 'pos1 'apt1 'cit1)
(unload-truck 'obj21 'tru2 'apt2)
(load-truck 'obj13 'tru4 'apt4)
(drive-truck 'tru4 'apt4 'pos4 'cit4)
(unload-truck 'obj13 'tru4 'pos4)
(fly-airplane 'apn1 'apt4 'apt1)
(fly-airplane 'apn1 'apt1 'apt2)
(load-airplane 'obj21 'apn1 'apt2)
(drive-truck 'tru4 'pos4 'apt4 'cit4)
(drive-truck 'tru1 'apt1 'pos1 'cit1)
(fly-airplane 'apn1 'apt2 'apt4)
(unload-airplane 'obj21 'apn1 'apt4)
(load-truck 'obj12 'tru1 'pos1)
(unload-truck 'obj23 'tru2 'apt2)
(load-truck 'obj21 'tru4 'apt4)
(drive-truck 'tru4 'apt4 'pos4 'cit4)
(unload-truck 'obj21 'tru4 'pos4)
(fly-airplane 'apn1 'apt4 'apt1)
(drive-truck 'tru1 'pos1 'apt1 'cit1)
(unload-truck 'obj12 'tru1 'apt1)
(load-airplane 'obj12 'apn1 'apt1)
(fly-airplane 'apn1 'apt1 'apt2)
(unload-airplane 'obj12 'apn1 'apt2)
(load-airplane 'obj23 'apn1 'apt2)
(fly-airplane 'apn1 'apt2 'apt1)
(unload-airplane 'obj23 'apn1 'apt1)
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
Real time: 0.248965 sec.
Run time: 0.248811 sec.
Space: 82771712 Bytes
GC: 38, GC time: 0.123798 sec.
"compiling..." Checking logistics3 (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Logistics3/logistics3.agda).
agda: Heap exhausted;
agda: Current maximum heap size is 3758096384 bytes (3584 MB).
agda: Use `+RTS -M<size>' to increase it.

Real time: 805.5584 sec.
Run time: 6.1E-5 sec.
Space: 368 Bytes
||#

