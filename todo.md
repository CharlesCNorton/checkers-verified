# Checkers Verified — TODO

1. Fix deprecated `Nat.mod_mul` → `Div0.mod_mul`
2. Rename `complete_game_verified` to something honest like `game_section_complete`
3. Split into multiple files with proper `Require Import`
4. Prove NoDup of captured positions within a valid chain
5. Prove `WFState` preservation: `apply_move_impl st m = Some st' → WFState st → WFState st'`
6. Prove `gen_steps` completeness: every legal step is in `gen_steps st`
7. Prove `gen_steps` soundness without requiring caller to supply `exists_jump_any = false`
8. Prove `gen_jumps` soundness: every move in `gen_jumps st` is legal
9. Prove `gen_jumps` completeness: every legal jump is in `gen_jumps st`
10. Prove `move_generation_complete`: `legal_move_impl st m = true → In m (generate_moves_impl st)`
11. Prove `reachable_preserves_wf` using (5) and transitivity of `reachable`
12. Wire `position_key_eqb_full` into repetition detection instead of hash-only comparison
13. Prove that `position_key_eqb_full = true → board_eq` (soundness of full comparison)
14. Prove `captures_removed_after_chain_only`: every over-square is occupied before and empty after apply
15. Prove `ballots_preserve_balance`: opening ballots preserve `WFState` and correct turn
16. Prove general `parse_print_inverse` for all legal moves, not just "9-14"
17. Extend `is_insufficient_material` to cover 2K vs lone K and other known dead positions
18. Extend verified game to a complete transcript from opening to terminal state
19. Add at least a probabilistic collision bound statement for Zobrist, or replace hash comparison with full comparison everywhere
20. Replace `vm_compute` proofs with structural proofs where feasible
21. Add extraction target (OCaml or Haskell) with a runnable game loop
