;
; Domain: Logistics (Version 1 - no typing)
;
; Author: Ron Petrick
;
; A simple logistics domain involving packages that
; need to be moved between different locations
; using different modes of transportation. Trucks can
; move packages within cities and airplanes can move
; packages between cities.
;
(define (domain logistics)
    (:requirements
        :strips
    )

    (:predicates
        (package ?p)
        (truck ?t1)
        (airplane ?p)
        (airport ?a)
        (city ?c)
        (vehicle ?v)
        (location ?l)

        (isAt ?x ?l)
        (inCity ?l ?c)
        (inVehicle ?p ?v)
    )

    (:action load
        :parameters
            (?p ?v ?l)
        :precondition
            (and
                (package ?p)
                (vehicle ?v)
                (location ?l)
		        (isAt ?v ?l)
                (isAt ?p ?l)
            )
        :effect
            (and
                (inVehicle ?p ?v)
                (not (isAt ?p ?l))
            )
    )

    (:action unload
        :parameters
            (?p ?v ?l)
        :precondition
            (and
                (package ?p)
                (vehicle ?v)
                (location ?l)
		        (isAt ?v ?l)
                (inVehicle ?p ?v)
            )
        :effect
            (and
                (isAt ?p ?l)
                (not (inVehicle ?p ?v))
            )
    )

    (:action drive
        :parameters
            (?t1 ?c ?l1 ?l2)
        :precondition
            (and
                (truck ?t1)
                (city ?c)
                (location ?l1)
                (location ?l2)
                (inCity ?l1 ?c)
                (inCity ?l2 ?c)
		        (isAt ?t1 ?l1)
            )
        :effect
            (and
                (isAt ?t1 ?l2)
                (not (isAt ?t1 ?l1))
            )
    )

    (:action fly
        :parameters
            (?p ?a1 ?a2)
        :precondition
            (and
                (airplane ?p)
                (airport ?a1)
                (airport ?a2)
		        (isAt ?p ?a1)
            )
        :effect
            (and
                (isAt ?p ?a2)
                (not (isAt ?p ?a1))
            )
    )
)
