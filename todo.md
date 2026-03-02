# Checkers Verified — TODO

1. Prove `gen_jumps` soundness: every move in `gen_jumps st` is legal
2. Prove `gen_jumps` completeness: every legal jump is in `gen_jumps st`
3. Prove `move_generation_complete`: `legal_move_impl st m = true → In m (generate_moves_impl st)`
4. Prove `reachable_preserves_wf` using WFState preservation and transitivity of `reachable`
5. Wire `position_key_eqb_full` into repetition detection instead of hash-only comparison
6. Prove that `position_key_eqb_full = true → board_eq` (soundness of full comparison)
7. Prove `captures_removed_after_chain_only`: every over-square is occupied before and empty after apply
8. Prove `ballots_preserve_balance`: opening ballots preserve `WFState` and correct turn
9. Prove general `parse_print_inverse` for all legal moves, not just "9-14"
10. Extend `is_insufficient_material` to cover 2K vs lone K and other known dead positions
11. Extend verified game to a complete transcript from opening to terminal state
12. Add at least a probabilistic collision bound statement for Zobrist, or replace hash comparison with full comparison everywhere
13. Replace `vm_compute` proofs with structural proofs where feasible
14. Split into multiple files with proper `Require Import`
15. Add extraction target (OCaml or Haskell) with a runnable game loop
