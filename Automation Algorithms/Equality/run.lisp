(setq domainfile "fab-domain.pddl")
(setq problemfile "fab-problem.pddl")
(setq outputfile "fab")

(setq plan '((pickup_from_table 'a)
             (putdown_on_stack 'a 'b)))

(time
  (progn
    (load "convert_agda")
    (load "solver")))

(print "type checking...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

;Real time: 0.088123 sec.
;Run time: 0.087967 sec.
;Space: 16793288 Bytes
;GC: 18, GC time: 0.024597 sec.
;"compiling..." Checking mprime (/home/alasdair/Documents/Sep_PDDL/New Code/Equality/mprime.agda).
;Real time: 44.589264 sec.
;Run time: 1.03E-4 sec.
;Space: 360 Bytes
