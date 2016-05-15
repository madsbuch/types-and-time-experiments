# LBS Project
A DSL for prevention of timing attacks.

## Assumptions
Not all data can be considered private. This is a too restrictive assumption
and would imposing constant runtime for all programs. This is of course not
possible. In the end information would be leaked in whether an answer is
produced or not.

__Data size as public information:__  Our approach is in turn the let the
data size be a public variable. The idea is, that if an algorithm takes
two instances of same-sized data, it will have the same runtime.

One way to carry it out is to

Evidently there are some restriction. Recursion in positionally modeled
numbers is not possible: _1111_ would run 15 times where 100 would run 7
times. The numbers have the same size. For numbers this can be overcome
by representing them by as Peano numerals.

For above reason general recursion is not possible. Hence we limit to
only do recursion in structures

## Application
Due to above restrictions it is not feasible to make a general purpose
programming language. We have therefor looked into some applications
where such a programming language could be used.

### Auction
The setting is as follows: A company needs to auction out a product, let's
say plane tickets. This is done by having a server, where all customers may
run their own code with their own rules for when to buy a plane ticket.

The customers should in their code provide a function, `buy :: Ticket -> Bool`,
which returns whether the company wants to buy a ticket, or not.

This service needs to be able to connect to a "home server" for information.

Based on above requirement, we can now define a DSL

__General types and associated operations:__

* Boolean
    - `and :: Boolean -> Boolean -> Boolean`
    - `or  :: Boolean -> Boolean -> Boolean`
    - `not :: Boolean -> Boolean`
    - `if  ::`
* Integer - +, -, *, /, equal, gt, gte
* Character - equals, gt, gte
* List - append, concat, ... __Size of a list i public information__

__Domain specific types and operations:__

* Webcall


