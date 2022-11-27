(setq domainfile "satellite-domain.pddl")
(setq problemfile "satellite-problem.pddl")
(setq outputfile "satellite3")

;plan length 44
(setq plan '(
(turn_to 'satellite4 'star11 'phenomenon9)
(turn_to 'satellite1 'star4 'groundstation3)
(turn_to 'satellite0 'phenomenon9 'star8)
(turn_to 'satellite2 'star0 'star4)
(switch_on 'instrument5 'satellite2)
(calibrate 'satellite2 'instrument5 'star0)
(turn_to 'satellite2 'star2 'star0)
(turn_to 'satellite2 'star5 'star2)
(turn_to 'satellite2 'planet6 'star5)
(turn_to 'satellite2 'phenomenon7 'planet6)
(turn_to 'satellite2 'star8 'phenomenon7)
(turn_to 'satellite2 'star10 'star8)
(take_image 'satellite2 'star10 'instrument5 'thermograph2)
(turn_to 'satellite2 'planet13 'star10)
(take_image 'satellite2 'planet13 'instrument5 'spectrograph4)
(turn_to 'satellite2 'planet14 'planet13)
(take_image 'satellite2 'planet14 'instrument5 'thermograph2)
(turn_to 'satellite3 'star2 'phenomenon9)
(switch_on 'instrument7 'satellite3)
(calibrate 'satellite3 'instrument7 'star2)
(turn_to 'satellite3 'star5 'star2)
(take_image 'satellite3 'star5 'instrument7 'image3)
(turn_to 'satellite3 'star8 'star5)
(take_image 'satellite3 'star8 'instrument7 'image3)
(turn_to 'satellite3 'planet16 'star8)
(take_image 'satellite3 'planet16 'instrument7 'image3)
(turn_to 'satellite4 'phenomenon15 'star11)
(turn_to 'satellite4 'star17 'phenomenon15)
(turn_to 'satellite4 'star2 'star17)
(switch_on 'instrument8 'satellite4)
(calibrate 'satellite4 'instrument8 'star2)
(turn_to 'satellite4 'planet6 'star2)
(take_image 'satellite4 'planet6 'instrument8 'infrared1)
(turn_to 'satellite4 'star11 'planet6)
(take_image 'satellite4 'star11 'instrument8 'infrared1)
(turn_to 'satellite4 'phenomenon15 'star11)
(take_image 'satellite4 'phenomenon15 'instrument8 'infrared0)
(turn_to 'satellite4 'star11 'phenomenon15)
(turn_to 'satellite4 'star17 'star11)
(take_image 'satellite4 'star17 'instrument8 'infrared0)
(turn_to 'satellite4 'star11 'star17)
(turn_to 'satellite4 'phenomenon7 'star11)
(take_image 'satellite4 'phenomenon7 'instrument8 'infrared1)
(turn_to 'satellite4 'star11 'phenomenon7)
))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

#||
Real time: 0.288276 sec.
Run time: 0.287021 sec.
Space: 111638688 Bytes
GC: 51, GC time: 0.165396 sec.
"compiling..." Checking satellite3 (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Satellite3/satellite3.agda).
agda: Heap exhausted;
agda: Current maximum heap size is 3758096384 bytes (3584 MB).
agda: Use `+RTS -M<size>' to increase it.

Real time: 790.23145 sec.
Run time: 1.22E-4 sec.
Space: 368 Bytes

||#

