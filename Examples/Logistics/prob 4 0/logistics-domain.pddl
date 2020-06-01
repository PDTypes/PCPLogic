;; logistics domain
;;

(define (domain logistics)
  (:requirements :strips) 
  (:predicates 	(package ?obj)
	       	(truck ?truck1)
		(airplane ?airplane1)
                (airport ?airport)
               	(location ?loc)
		(in-city ?obj ?city1)
                (city ?city1)
		(at ?obj ?loc)
		(isin ?obj ?obj))

 
(:action load-truck
  :parameters
   (?obj
    ?truck1
    ?loc)
  :precondition
   (and (package ?obj) (truck ?truck1) (location ?loc)
   (at ?truck1 ?loc) (at ?obj ?loc))
  :effect
   (and (not (at ?obj ?loc)) (isin ?obj ?truck1)))

(:action load-airplane
  :parameters
   (?obj
    ?airplane1
    ?loc)
  :precondition
   (and (package ?obj) (airplane ?airplane1) (location ?loc)
   (at ?obj ?loc) (at ?airplane1 ?loc))
  :effect
   (and (not (at ?obj ?loc)) (isin ?obj ?airplane1)))

(:action unload-truck
  :parameters
   (?obj
    ?truck1
    ?loc)
  :precondition
   (and (package ?obj) (truck ?truck1) (location ?loc)
        (at ?truck1 ?loc) (isin ?obj ?truck1))
  :effect
   (and (not (isin ?obj ?truck1)) (at ?obj ?loc)))

(:action unload-airplane
  :parameters
   (?obj
    ?airplane1
    ?loc)
  :precondition
   (and (package ?obj) (airplane ?airplane1) (location ?loc)
        (isin ?obj ?airplane1) (at ?airplane1 ?loc))
  :effect
   (and (not (isin ?obj ?airplane1)) (at ?obj ?loc)))

(:action drive-truck
  :parameters
   (?truck1
    ?loc-from
    ?loc-to
    ?city1)
  :precondition
   (and (truck ?truck1) (location ?loc-from) (location ?loc-to) (city ?city1)
   (at ?truck1 ?loc-from)
   (in-city ?loc-from ?city1)
   (in-city ?loc-to ?city1))
  :effect
   (and (not (at ?truck1 ?loc-from)) (at ?truck1 ?loc-to)))

(:action fly-airplane
  :parameters
   (?airplane1
    ?loc-from
    ?loc-to)
  :precondition
   (and (airplane ?airplane1) (airport ?loc-from) (airport ?loc-to)
	(at ?airplane1 ?loc-from))
  :effect
   (and (not (at ?airplane1 ?loc-from)) (at ?airplane1 ?loc-to)))
)