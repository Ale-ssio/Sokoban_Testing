/* SOKOBAN */

/*
  1. controller(example): debug controller, executes predefined actions.
  2. controller(wander): debug controller, executes move action until it is in a certain cell.
  3. controller(dumb): dumb controller, executes non-deterministic moves until it reaches the goal.
  ...
*/

:- dynamic controller/1.
:- discontiguous
    right/2,
    left/2,
    up/2,
    down/2,
    fun_fluent/1,
    rel_fluent/1,
    initially/2,
    proc/2,
    causes_true/3,
    causes_false/3.

% There is nothing to do caching on (required because cache/1 is static)
cache(_) :- fail.

/* Domain. */

% Cells.
loc(c00). loc(c01). loc(c02). loc(c03). loc(c04).
loc(c10). loc(c11). loc(c12). loc(c13). loc(c14).
loc(c20). loc(c21). loc(c22). loc(c23). loc(c24).
loc(c30). loc(c31). loc(c32). loc(c33). loc(c34).
loc(c40). loc(c41). loc(c42). loc(c43). loc(c44).

% Targets (still cells).
loc(T) :- trg(T).
trg(c24).

% Boxes.
box(b1).

% Walls.
wall(w1). wall(w2). wall(w3).

% Objects (boxes and walls).
obj(O) :- box(O).
obj(O) :- wall(O).

/* Adjacency. */

left(c00,c01).  up(c00,c10).
right(c01,c00). left(c01,c02).  up(c01,c11).
right(c02,c01). left(c02,c03).  up(c02,c12).
right(c03,c02). left(c03,c04).  up(c03,c13).
right(c04,c03). up(c04,c14).

left(c10,c11).  up(c10,c20).    down(c10,c00).
right(c11,c10). left(c11,c12).  up(c11,c21).    down(c11,c01).
right(c12,c11). left(c12,c13).  up(c12,c22).    down(c12,c02).
right(c13,c12). left(c13,c14).  up(c13,c23).    down(c13,c03).
right(c14,c13). up(c14,c24).    down(c14,c04).

left(c20,c21).  up(c20,c30).    down(c20,c10).
right(c21,c20). left(c21,c22).  up(c21,c31).    down(c21,c11).
right(c22,c21). left(c22,c23).  up(c22,c32).    down(c22,c12).
right(c23,c22). left(c23,c24).  up(c23,c33).    down(c23,c13).
right(c24,c23). up(c24,c34).    down(c24,c14).

left(c30,c31).  up(c30,c40).    down(c30,c20).
right(c31,c30). left(c31,c32).  up(c31,c41).    down(c31,c21).
right(c32,c31). left(c32,c33).  up(c32,c42).    down(c32,c22).
right(c33,c32). left(c33,c34).  up(c33,c43).    down(c33,c23).
right(c34,c33). up(c34,c44).    down(c34,c24).

left(c40,c41).  up(c40,c50).    down(c40,c30).
right(c41,c40). left(c41,c42).  up(c41,c51).    down(c41,c31).
right(c42,c41). left(c42,c43).  up(c42,c52).    down(c42,c32).
right(c43,c42). left(c43,c44).  up(c43,c53).    down(c43,c33).
right(c44,c43). up(c44,c54).    down(c44,c34).

left(c50,c51).  down(c50,c40).
right(c51,c50). left(c51,c52).  down(c51,c41).
right(c52,c51). left(c52,c53).  down(c52,c42).
right(c53,c52). left(c53,c54).  down(c53,c43).
right(c54,c53). down(c54,c44).

/* Helping predicates. */

% adj(L1,L2): checks whether L1 and L2 are adjacent locations.
adj(L1,L2) :- right(L1,L2).
adj(L1,L2) :- left(L1,L2).
adj(L1,L2) :- up(L1,L2).
adj(L1,L2) :- down(L1,L2).

% pushable(L1,L2,L3): checks whether L1, L2 and L3 are positioned in a way that allows a push.
pushable(L1,L2,L3) :- up(L1,L2), down(L3,L2).
pushable(L1,L2,L3) :- down(L1,L2), up(L3,L2).
pushable(L1,L2,L3) :- left(L1,L2), right(L3,L2).
pushable(L1,L2,L3) :- right(L1,L2), left(L3,L2).

/* Fluents and causal laws. */

% self_at(L): true if the agent is in location L.
rel_fluent(self_at(L)) :- loc(L). 
causes_true(move(_L1,L2), self_at(L2), true).
causes_true(push(_B,_L1,L2,_L3), self_at(L2), true).
causes_false(move(L1,_L2), self_at(L1), true).
causes_false(push(_B,L1,_L2,_L3), self_at(L1), true).

% at(O,L): true if object O is in location L.
rel_fluent(at(O,L)) :- obj(O), loc(L).
causes_true(push(O,_L1,_L2,L3), at(O,L3), true).
causes_false(push(O,_L1,L2,_L3), at(O,L2), true).

/* Helping fluents. */

/* We need these because in procedures we can only use fluents and not predicates. */

% Define a fluent that is always true when locations are adjacent.
rel_fluent(adjacent(L1,L2)) :- loc(L1), loc(L2).

% Define a fluent that is always true when locations are in line to allow pushing.
rel_fluent(in_line(L1,L2,L3)) :- loc(L1), loc(L2), loc(L3).

% Define a fluent that is true when location L is empty (no agent, no objects).
rel_fluent(empty(L)) :- loc(L).
causes_true(move(L1,_L2), empty(L1), true).
causes_true(push(_B,L1,_L2,_L3), empty(L1), true).
causes_false(move(_L1,L2), empty(L2), true).
causes_false(push(_B,_L1,_L2,L3), empty(L3), true).

/* Primitive actions and preconditions. */

% move(L1,L2): the agent goes from location L1 to location L2.
prim_action(move(L1,L2)) :- loc(L1), loc(L2).
poss(move(L1,L2), (self_at(L1),
                   adjacent(L1,L2),
                   empty(L2))).

% push(B,L1,L2,L3): the agent pushes box B from L2 to L3, while moving from L1 to L2.
prim_action(push(B,L1,L2,L3)) :- box(B), loc(L1), loc(L2), loc(L3).
poss(push(B,L1,L2,L3), (self_at(L1),
                        at(B,L2),
                        empty(L3),
                        in_line(L1,L2,L3))).

/* Initial state. */

% Agent.
initially(self_at(c42), true).

% Boxes.
initially(at(b1,c11), true).

% Walls.
initially(at(w1,c21), true).
initially(at(w2,c22), true).
initially(at(w3,c23), true).

% Helpers.
initially(adjacent(L1,L2), true) :- adj(L1,L2).
initially(in_line(L1,L2,L3), true) :- pushable(L1,L2,L3).
initially(empty(L), true) :-
    loc(L),
    \+ initially(self_at(L), true),
    \+ (obj(O), initially(at(O,L), true)).

/* Procedures. */

% some_boxes_not_on_trg: check whether there are some boxes still not on target cells.
proc(some_boxes_not_on_trg,
  some(b, and(box(b), 
              neg(some(t, and(trg(t), at(b,t))))))
).

% move_somewhere: from the current cell, move to a non-deterministic adjacent cell.
proc(move_somewhere,
  pi(l1, [
    ?(self_at(l1)),
    pi(l2, move(l1, l2))
  ])
).

% push_something: 
proc(push_something,
  pi(b, pi(l1, pi(l2, pi(l3, [
    ?(in_line(l1,l2,l3)),
    ?(self_at(l1)),
    ?(at(b,l2)),
    push(b, l1, l2, l3)
  ]))))
).

% do_something: non-deterministically picks one between move somewhere and push something.
proc(do_something,
  ndet(move_somewhere, push_something)
).

/* Controllers. */

% Debug controller: fix some actions to monitor the execution.
proc(control(example), search(example)).
proc(example, [ 
  move(c40, c30),
  move(c30, c20),
  move(c20, c10),
  push(b1, c10, c11, c12) 
]).

% Wander controller: non-deterministically picks actions until the condition is satisfied.
proc(control(wander), search(wander)).
proc(wander, [
  star(move_somewhere),
  ?(self_at(c02))
]).

% Dumb controller: non-deterministically picks actions until all the boxes are on targets.
proc(control(dumb), search(dumb)).
proc(dumb, [
  star(do_something),
  ?(neg(some_boxes_not_on_trg))
]).