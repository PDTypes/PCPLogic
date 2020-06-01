(define (domain blocksworld)
(:requirements :strips :equality)
(:predicates
(handEmpty)
(holding ?x)
(onTable ?x)
(on ?x ?y)
(clear ?x))

(:action pickup_from_table
:parameters
(?x)
:precondition
(and (handEmpty)
(onTable ?x)
(clear ?x))
:effect
(and (not (handEmpty))
(not (onTable ?x))
(holding ?x)))

(:action putdown_on_stack
:parameters
(?x ?y)
:precondition
(and
(not (= ?x ?y))
(holding ?x)
(clear ?y))
:effect
(and
(not (holding ?x))
(not (clear ?y))
(on ?x ?y)
(handEmpty))))
