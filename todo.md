# Checkers Verified — TODO

1. Prove `WFState` preservation: `apply_move_impl st m = Some st' → WFState st → WFState st'`
2. Prove `gen_steps` completeness: every legal step is in `gen_steps st`
3. Prove `gen_steps` soundness without requiring caller to supply `exists_jump_any = false`
4. Prove `gen_jumps` soundness: every move in `gen_jumps st` is legal
5. Prove `gen_jumps` completeness: every legal jump is in `gen_jumps st`
6. Prove `move_generation_complete`: `legal_move_impl st m = true → In m (generate_moves_impl st)`
7. Prove `reachable_preserves_wf` using (1) and transitivity of `reachable`
8. Wire `position_key_eqb_full` into repetition detection instead of hash-only comparison
9. Prove that `position_key_eqb_full = true → board_eq` (soundness of full comparison)
10. Prove `captures_removed_after_chain_only`: every over-square is occupied before and empty after apply
11. Prove `ballots_preserve_balance`: opening ballots preserve `WFState` and correct turn
12. Prove general `parse_print_inverse` for all legal moves, not just "9-14"
13. Extend `is_insufficient_material` to cover 2K vs lone K and other known dead positions
14. Extend verified game to a complete transcript from opening to terminal state
15. Add at least a probabilistic collision bound statement for Zobrist, or replace hash comparison with full comparison everywhere
16. Replace `vm_compute` proofs with structural proofs where feasible
17. Split into multiple files with proper `Require Import`
18. Add extraction target (OCaml or Haskell) with a runnable game loop
