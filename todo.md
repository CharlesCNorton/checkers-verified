# Checkers Verified — TODO

1. Split into multiple files with proper `Require Import`
2. Prove NoDup of captured positions within a valid chain
3. Prove `WFState` preservation: `apply_move_impl st m = Some st' → WFState st → WFState st'`
4. Prove `gen_steps` completeness: every legal step is in `gen_steps st`
5. Prove `gen_steps` soundness without requiring caller to supply `exists_jump_any = false`
6. Prove `gen_jumps` soundness: every move in `gen_jumps st` is legal
7. Prove `gen_jumps` completeness: every legal jump is in `gen_jumps st`
8. Prove `move_generation_complete`: `legal_move_impl st m = true → In m (generate_moves_impl st)`
9. Prove `reachable_preserves_wf` using (3) and transitivity of `reachable`
10. Wire `position_key_eqb_full` into repetition detection instead of hash-only comparison
11. Prove that `position_key_eqb_full = true → board_eq` (soundness of full comparison)
12. Prove `captures_removed_after_chain_only`: every over-square is occupied before and empty after apply
13. Prove `ballots_preserve_balance`: opening ballots preserve `WFState` and correct turn
14. Prove general `parse_print_inverse` for all legal moves, not just "9-14"
15. Extend `is_insufficient_material` to cover 2K vs lone K and other known dead positions
16. Extend verified game to a complete transcript from opening to terminal state
17. Add at least a probabilistic collision bound statement for Zobrist, or replace hash comparison with full comparison everywhere
18. Replace `vm_compute` proofs with structural proofs where feasible
19. Add extraction target (OCaml or Haskell) with a runnable game loop
