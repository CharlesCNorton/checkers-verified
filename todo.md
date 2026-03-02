# Checkers Verified — TODO

1. Prove `gen_jumps` completeness: every legal jump is in `gen_jumps st`
2. Prove `move_generation_complete`: `legal_move_impl st m = true → In m (generate_moves_impl st)`
3. Prove `reachable_preserves_wf` using WFState preservation and transitivity of `reachable`
4. Wire `position_key_eqb_full` into repetition detection instead of hash-only comparison
5. Prove that `position_key_eqb_full = true → board_eq` (soundness of full comparison)
6. Prove `captures_removed_after_chain_only`: every over-square is occupied before and empty after apply
7. Prove `ballots_preserve_balance`: opening ballots preserve `WFState` and correct turn
8. Prove general `parse_print_inverse` for all legal moves, not just "9-14"
9. Extend `is_insufficient_material` to cover 2K vs lone K and other known dead positions
10. Extend verified game to a complete transcript from opening to terminal state
11. Add at least a probabilistic collision bound statement for Zobrist, or replace hash comparison with full comparison everywhere
12. Replace `vm_compute` proofs with structural proofs where feasible
13. Split into multiple files with proper `Require Import`
14. Add extraction target (OCaml or Haskell) with a runnable game loop
