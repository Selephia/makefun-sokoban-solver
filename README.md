# Sokoban solver — make.fun bounty entry

A push-optimal Sokoban solver for make.fun's "Build the best Sokoban solver"
bounty (sokoban-solver-01-run-20261121). Single file: `main.ts`, plain
JavaScript, Node 22, no dependencies.

## How it works

Levels from this generator are a hallway with independent rooms hanging off
it: a box pushed out of its room can never reach a goal, so a level's optimal
push count is the sum of its rooms' optima.

1. Parse the XSB level; compute the "live" squares (a box alone on them can
   still be pushed onto a goal) by reverse pull-back from the goals.
2. Cut the non-live squares of the player's row (the hallway) and split the
   remaining floor into components — each component holding boxes is a room.
3. Solve rooms one at a time on the full board, with the other rooms' boxes
   standing as walls (a finished room's boxes stand on their goals). Each
   room is solved with a breadth-first search over pushes — state = sorted
   box squares plus the lowest square of the player's reachable region —
   pruned by dead squares and frozen 2x2 blocks, so the first solution found
   is push-optimal. If a search ever exhausts its state budget, an A* with a
   minimum-cost box–goal matching heuristic, then a greedy best-first
   search, take over for that room.
4. All limits are counts of states, never the clock: two runs on the same
   input write byte-identical answers.

## Local run

```
mkdir -p out
MAKEFUN_INPUT_DIR=<dir with i001..i005/level.txt> MAKEFUN_OUTPUT_DIR=out node main.ts
```

Answers land in `out/<id>/solution.txt` (LURD moves, uppercase = push).
