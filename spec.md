ENGLISH DRAUGHTS (CHECKERS) — FORMAL SPECIFICATION WITH VALIDATION

SECTION 1: FOUNDATIONS AND METATHEORY

* Imports:

  * `Coq.Program.Program`, `Coq.Vectors.Fin`, `Coq.Logic.Decidable`,
    `Coq.Logic.FunctionalExtensionality`, `Coq.Logic.Classical`,
    `Coq.Lists.List`, `Coq.MSets.MSetInterface` (or FSets for sets of squares).
* Custom tactics for:

  * case splits on colors, piece kinds, options; rewriting extensional equalities.
* Setoid infrastructure:

  * Extensional equality for boards: `board_eq b1 b2 := forall p, b1 p = b2 p`.
  * Proper instances for update operations and predicates.
* Global notation reservations:

  * Square indices `⟦1..32⟧`, directions, `·` for function application, `∅` for empty set.
* Proof-mode configuration:

  * `Set Implicit Arguments.`, `Generalizable All Variables.`, `Set Universe Polymorphism.`

VALIDATION:

```coq
Lemma bool_decidable : forall b:bool, {b = true} + {b = false}.
```

---

SECTION 2: FINITE DOMAIN THEORY

* `Fin8 : Fin.t 8` with complete enumeration `enum_fin8 : list (Fin.t 8)` and `NoDup`.
* `Finite` typeclass with instances for `Fin.t n`, `bool`, `Color`, `PieceKind`.
* Decidable equality instances for all base types (`EqDec`).
* Exhaustive case analysis principles for `Color`, `PieceKind`, `Fin.t n`.
* Bijection with bounded nat:

  * `fin8_of_nat : { n | n < 8 } -> Fin.t 8`.
  * `nat_of_fin8 : Fin.t 8 -> { n | n < 8 }`.
* Integer embeddings: `fileZ, rankZ : Fin.t 8 -> Z`.

VALIDATION:

```coq
Lemma all_fin8_in_enumeration : forall (f : Fin.t 8), In f enum_fin8.
```

---

SECTION 3: POSITION ABSTRACTION (DARK-SQUARE SUBSET OF 8×8)

* Abstract module `Position`:

  * Types: `Rank := Fin.t 8`, `File := Fin.t 8`.
  * Predicate `dark : Rank -> File -> bool` marking playable squares (32 dark squares).
  * Opaque `Position` as `{ rf : Rank * File | dark (fst rf) (snd rf) = true }`.
* Constructors/destructors:

  * `mk_pos : Rank -> File -> option Position`.
  * Projections `rank : Position -> Rank`, `file : Position -> File`.
* Enumeration:

  * `enum_pos : list Position` (size 32) with `NoDup_enum_pos` and completeness.
* Coordinate arithmetic (safe):

  * `off : Position -> Z (*dr*) -> Z (*df*) -> option Position`
    with reversibility lemma when in-bounds and dark.
* Numeric square indexing (1..32):

  * `sq_index : Position -> { n | 1 <= n <= 32 }` and inverse `pos_of_index`.

VALIDATION:

```coq
Example offset_roundtrip :
  forall p dr df p',
    off p dr df = Some p' ->
    off p' (-dr) (-df) = Some p.
```

---

SECTION 4: CORE GAME ONTOLOGY

* Colors: `Color := Dark | Light.`  (\* Dark moves first. \*)
* Piece kinds: `PieceKind := Man | King.`
* Piece record: `Piece := { pc_color : Color; pc_kind : PieceKind }`.
* Functions:

  * `opp : Color -> Color` with `opp (opp c) = c`.
* Decidable equality for all above.
* Exhaustiveness lemmas for case analysis on colors and kinds.

VALIDATION:

```coq
Example opposite_color_involutive : forall c, opp (opp c) = c.
```

---

SECTION 5: BOARD ABSTRACTION

* Board as total map on playable squares:

  * `Board := Position -> option Piece`.
* Board extensional equality:

  * `board_eq b1 b2 := forall p, b1 p = b2 p`. (Setoid.)
* Updates:

  * `board_set : Board -> Position -> option Piece -> Board`.
  * `board_get b p := b p`.
  * Update properties: idempotence, commutativity on distinct squares, extensionality.
* Predicates:

  * `occupied b p`, `occupied_by b c p`.
  * `on_dark_only` invariant (trivial by construction of `Position`).
* Initial position:

  * Numeric mapping `pos_of_index : { n | 1 <= n <= 32 } -> Position`.
  * `initial_board : Board` places Dark men on squares 1..12, Light men on 21..32.

VALIDATION:

```coq
Example board_update_retrieve :
  forall b p pc, board_get (board_set b p (Some pc)) p = Some pc.
```

---

SECTION 6: MOVEMENT GEOMETRY (DIAGONALS ON DARK SQUARES)

* Primitive neighbor relations:

  * `diag_adj : Position -> Position -> Prop` (distance 1 diagonal).
  * `diag_jump : Position -> Position -> Position -> Prop`
    (\* from, over, to: distance-2 diagonal with over as the middle square \*).

* Directionality:

  * `forward_of (c:Color) (r1 r2:Rank) : Prop`
    (\* for Dark: increasing rank; for Light: decreasing rank; derived via rankZ \*).

* Step moves (non-capturing):

  * `step_man c from to : Prop` iff `diag_adj from to` and `to` is forward for color `c`.
  * `step_king from to : Prop` iff `diag_adj from to` (any diagonal, both senses).
  * No “flying”: steps are exactly distance 1.

* Jump moves (capturing primitives):

  * `jump_man c from over to : Prop` iff
    `diag_jump from over to`, `over` is adjacent and **forward** w\.r.t. `from->to` for `c`,
    and geometry matches (no backward capture for Man).
  * `jump_king from over to : Prop` iff `diag_jump from over to` (any direction).

VALIDATION:

```coq
Example king_step_is_diagonal :
  forall from to, step_king from to -> diag_adj from to.

Example man_cannot_step_backward :
  forall c from to, step_man c from to -> forward_of c (rank from) (rank to).
```

---

SECTION 7: PIECE MOVEMENT RULES (PATTERNS ONLY)

* Specifications:

  * `man_step_spec`, `king_step_spec` for distance-1 moves (no occupancy yet).
  * `man_jump_spec`, `king_jump_spec` asserting exact 2-diagonal geometry.

* Implementation predicates over a board:

  * `step_impl (b:Board) (pc:Piece) (from to:Position) : bool`
    (\* checks empty destination, pattern matches PieceKind & direction, and **no capture** obligations block it (but see forcing in Section 9) \*).

  * `jump_impl (b:Board) (pc:Piece) (from over to:Position) : bool`
    (\* checks over contains opponent piece, landing empty, pattern matches \*).

* Man restrictions:

  * Non-capturing man moves forward only.
  * Capturing man jumps forward only (never backward).

VALIDATION:

```coq
Example king_nonflying :
  forall b c from to,
    step_impl b {|pc_color:=c; pc_kind:=King|} from to = true ->
    exists d, diag_adj from to /\ d = 1%Z.

Example man_jump_not_backward :
  forall b c from over to,
    pc_kind {|pc_color:=c; pc_kind:=Man|} = Man ->
    jump_impl b {|pc_color:=c; pc_kind:=Man|} from over to = true ->
    forward_of c (rank from) (rank to).
```

---

SECTION 8: CAPTURE CHAINS (MULTI-JUMP)

* Chains as sequences of `(over, to)` from an initial `from`:

  * `JumpLink := { over:Position & Position }`  (\* sigma pair (over,to) \*).
  * `JumpChain := list JumpLink`.

* Chain validity **relative to a board**:

  * `valid_jump_chain b pc from ch` iff

    1. For each `(over_i,to_i)` in order, `jump_impl` holds on the *current transient occupancy*,
    2. The *over* squares are pairwise distinct (cannot jump the same enemy twice),
    3. Landings are empty at their time of landing,
    4. For Man, each link is forward-only,
    5. Intermediate captured men/kings **remain on-board as blockers** during the chain (no reusing their squares),
    6. The final landing square is `to_last`.

* Terminality:

  * `chain_maximal b pc from ch` iff from the last landing, **no further legal jump** exists (w\.r.t. transient occupancy).

* **Promotion exception**:

  * If a Man’s last landing reaches crown-head, it promotes immediately and **the chain ends** even if further jumps would be available to a king.

* Set of captured squares of a chain:

  * `captures_of ch : list Position` (the `over` components).

VALIDATION:

```coq
Example captured_not_reusable_in_chain :
  forall b pc from ch over to,
    valid_jump_chain b pc from ch ->
    In over (map (fun l => projT1 l) ch) ->
    (* No later link can jump the same 'over' again *)
    NoDup (map (fun l => projT1 l) ch).

Example promotion_ends_chain :
  forall b from ch,
    valid_jump_chain b {|pc_color:=Dark; pc_kind:=Man|} from ch ->
    reaches_crown_head (last_landing from ch) = true ->
    chain_maximal b {|pc_color:=Dark; pc_kind:=Man|} from ch.
```

---

SECTION 9: FORCING RULES (MANDATORY CAPTURE)

* Availability predicates:

  * `exists_jump_from b c from : bool`.
  * `exists_jump_any b c : bool`.
* Forcing laws:

  * If `exists_jump_any b (turn st) = true` then **no** non-capturing move is legal.
  * During a chain, if another jump is available from the current landing, it **must** continue, unless promotion just occurred.
* Choice of path:

  * There is **no majority-capture** requirement; any legal chain may be chosen.

VALIDATION:

```coq
Example mandatory_capture_blocks_steps :
  forall st from to pc,
    side_to_move st = pc_color pc ->
    board st from = Some pc ->
    exists_jump_any (board st) (pc_color pc) = true ->
    step_impl (board st) pc from to = false.
```

---

SECTION 10: GAME STATE

* `GameState` record:

  * `board : Board`
  * `turn  : Color`  (\* Dark moves first in initial state \*)
  * `ply_without_capture_or_man_advance : nat`  (\* for Forty-Move Rule = 80 plies \*)
  * `repetition_book : multiset PositionKey` (\* hashable position key, see §18 \*)
  * Optional protocol flags (draw offer, etc.) kept outside core legality.
* Well-formedness:

  * Pieces only on dark squares (by `Position` construction).
  * Counts: initial ≤ 12 each; preserved constraints (cannot exceed 12).
  * `WFState st : Prop`.

VALIDATION:

```coq
Example initial_wellformed :
  WFState (initial_state).
```

---

SECTION 11: MOVE REPRESENTATION

* `Move`:

  * `Step : Position -> Position -> Move`                      (\* non-capturing \*)
  * `Jump : Position -> JumpChain -> Move`                     (\* capturing chain \*)
  * `Resign : Color -> Move`
  * `AgreeDraw : Move`  (\* protocol, optional to core legality \*)
* Accessors:

  * `move_src : Move -> option Position`.
  * `move_dst : Board -> Move -> option Position` (for chains uses last landing).
* Derived info:

  * `captures_of_move : Move -> list Position`.

VALIDATION:

```coq
Example move_roundtrip_step :
  forall from to, move_src (Step from to) = Some from /\ move_dst b (Step from to) = Some to.

Example jump_last_landing_defined :
  forall from ch, move_dst b (Jump from ch) = Some (last_landing from ch).
```

---

SECTION 12: MOVE LEGALITY

* Validation ordering:

  1. Source occupancy by side to move.
  2. Pattern check (step or jump link geometry).
  3. Destination emptiness / opponent at `over` for jumps.
  4. Forcing: if any jump exists, reject steps; for a chain, require maximality unless promotion ends it.
  5. No friendly capture; cannot jump same enemy twice in a chain.
  6. Promotion on reaching crown-head for Man (and **stop** chain).
* Specification:

  * `legal_move_spec : GameState -> Move -> Prop`.
* Implementation:

  * `legal_move_impl : GameState -> Move -> bool`.
  * Correctness & completeness lemmas relating `_impl` and `_spec`.

VALIDATION:

```coq
Example legal_requires_maximal_chain :
  forall st from ch,
    legal_move_impl st (Jump from ch) = true ->
    chain_maximal (board st) (piece_at (board st) from) from ch \/  (* ended by lack of further jumps *)
    (is_man (piece_at (board st) from) /\ reaches_crown_head (last_landing from ch) = true).

Example man_backward_capture_illegal :
  forall st from over to,
    (* building a single-link chain *)
    legal_move_impl st (Jump from (cons (existT _ over to) nil)) = true ->
    forward_of (turn st) (rank from) (rank to).
```

---

SECTION 13: APPLYING MOVES

* Transition function:

  * `apply_move_spec : GameState -> Move -> option GameState`.
  * Effects:

    1. For `Step from to`:

       * Move piece `from → to`, no captures.
       * If mover is Man and `to` is crown-head: promote to King.
       * Update `ply_without_capture_or_man_advance`: increment **if** the move was neither a capture nor a **Man forward step**; otherwise reset to 0.
       * Toggle `turn`.
    2. For `Jump from ch`:

       * Execute chain on transient board: keep captured enemies **present** as blockers during the chain.
       * At chain end, **remove all captured pieces at once**.
       * If the mover was a Man and last landing is crown-head: promote to King and **do not** continue jumping.
       * Reset `ply_without_capture_or_man_advance` to 0 (a capture occurred).
       * Toggle `turn`.
    3. For `Resign`, set terminal result accordingly.
* Implementation:

  * `apply_move_impl : GameState -> Move -> option GameState` with proofs of alignment with spec.

VALIDATION:

```coq
Example apply_legal_succeeds :
  forall st m,
    WFState st ->
    legal_move_impl st m = true ->
    exists st', apply_move_impl st m = Some st'.

Example captures_removed_after_chain_only :
  forall st from ch st',
    legal_move_impl st (Jump from ch) = true ->
    apply_move_impl st (Jump from ch) = Some st' ->
    (* Every 'over' square is empty in st' and was nonempty (opponent) in st *)
    forall o, In o (captures_of (Jump from ch)) ->
              occupied (board st) o = true /\ occupied (board st') o = false.
```

---

SECTION 14: MOVE GENERATION

* Pseudo-legal generation:

  * `gen_steps : GameState -> list Move`  (\* all step moves for side to move \*)
  * `gen_jumps : GameState -> list Move`  (\* all maximal jump chains from each source \*)
* Forcing filter:

  * If `gen_jumps` nonempty, legal moves are exactly the maximal jump chains.
  * Else legal moves are the steps.
* Final generator:

  * `generate_moves_impl : GameState -> list Move`.
  * No duplication; `NoDup` of generated moves.

VALIDATION:

```coq
Example gen_captures_all_legal :
  forall st m,
    WFState st ->
    legal_move_impl st m = true ->
    In m (generate_moves_impl st).
```

---

SECTION 15: GAME TREE PROPERTIES

* `reachable : GameState -> GameState -> Prop` via reflexive–transitive closure of legal moves.
* Preservation:

  * `WFState` preserved by `apply_move_impl` on legal moves.
* Finiteness:

  * Finite board & pieces ⇒ finite position space.
  * With Forty-Move Rule counter (80 plies), any sufficiently long play allows a **draw claim**.

VALIDATION:

```coq
Example reachable_preserves_wf :
  forall st st',
    WFState st ->
    reachable st st' ->
    WFState st'.
```

---

SECTION 16: TERMINAL CONDITIONS

* Win by elimination:

  * `has_no_pieces b c : bool`.
* Win by immobilization:

  * `has_no_legal_moves st : bool`.
  * If side to move has no legal moves → loses (opponent wins).
* Draw conditions (claim-based):

  * **Agreement**.
  * **Threefold repetition**: same `board` and `turn` occur three times in the game history.
  * **Forty-Move Rule**: if `ply_without_capture_or_man_advance >= 80`, either player may claim a draw.

Functions:

* `is_terminal : GameState -> option GameResult`  (\* if forced by elimination/immobilization only \*).

VALIDATION:

```coq
Example immobilization_loses :
  forall st,
    WFState st ->
    has_no_legal_moves st = true ->
    winner_if_terminal st = Some (opp (turn st)).
```

---

SECTION 17: OPTIONAL/HISTORICAL RULES

* Huffing (deprecated): modeled only as *illegal-move correction* outside core state.
* Three-move ballot openings:

  * `apply_opening_ballot : GameState -> Opening -> option GameState`.
  * Proof that ballots preserve `WFState`.
* Touch-move protocol omitted from core legality; may be formalized as meta-rules.

VALIDATION:

```coq
Example ballots_preserve_balance :
  forall st op st',
    WFState st ->
    apply_opening_ballot st op = Some st' ->
    WFState st' /\ turn st' = turn st. 
```

---

SECTION 18: VALIDATION FRAMEWORK & REPETITION KEYS

* Position key:

  * `PositionKey` hashing `board` & `turn` (ignoring counters).
  * `key_of_state : GameState -> PositionKey`.
* Repetition history:

  * Update multiset of keys after each applied move.
* Test suites:

  * Standard starting perft values (depth-limited node counts).
  * Problem positions for multi-jump correctness and promotion-exception.

VALIDATION:

```coq
Theorem repetition_detects_threefold :
  forall hist st,
    three_occurrences (key_of_state st) hist = true ->
    can_claim_threefold hist st = true.

Example perft_initial_depth2 :
  perft initial_state 2 = (* fill with computed reference *).
```

---

SECTION 19: NOTATION (PDN-STYLE)

* Square numbers 1..32 (`sq_index` ↔ `pos_of_index`).
* Non-capturing step notation: `a-b` (e.g., `9-14`).
* Captures: `axb[... ]x z` (e.g., `22x15x8`), chain enumerates landing squares.
* Printers/parsers:

  * `move_to_numeric : GameState -> Move -> string`.
  * `parse_numeric  : string -> GameState -> option Move`.
* Round-trip property on legal moves.

VALIDATION:

```coq
Theorem parse_print_inverse :
  forall st m,
    WFState st ->
    legal_move_impl st m = true ->
    parse_numeric (move_to_numeric st m) st = Some m.
```

---

SECTION 20: EVALUATION (OPTIONAL HEURISTICS)

* Material:

  * Man = 1, King = 2 (or 3) (parameterized).
* Positional:

  * Advancement (for men), center control, mobility (#legal moves), tempo.
* `evaluate : GameState -> Color -> Z`.
* Soundness:

  * Boundedness given max 24 pieces and chosen weights.

VALIDATION:

```coq
Example material_bounds :
  forall b c,
    0 <= material_value b c <= 24 * max_piece_weight.
```

---

SECTION 21: METATHEOREMS & IMPLEMENTATION CONTRACTS

* Decidability:

  * All core predicates (`WFState`, `legal_move_spec`, `valid_jump_chain`, `chain_maximal`) are decidable.
* Termination meta:

  * With the Forty-Move Rule claim, every infinite play admits a draw claim; hence practical termination under tournament law.
* Completeness & soundness:

  * `legal_move_impl` is equivalent to `legal_move_spec`.
  * `apply_move_impl` satisfies `apply_move_spec`.

VALIDATION:

```coq
Theorem no_infinite_forced_losses :
  forall st stream,
    WFState st ->
    (* any infinite legal play admits a draw claim if no capture/man advance happens *)
    eventually (fun st => ply_without_capture_or_man_advance st >= 80) stream ->
    can_claim_forty_move (last stream) = true.

Theorem move_generation_complete :
  forall st m,
    WFState st ->
    legal_move_impl st m = true ->
    In m (generate_moves_impl st).
```

---

IMPLEMENTATION REQUIREMENTS

1. Every function has spec/impl with correctness and (where applicable) completeness proofs.
2. Partial functions (`off`, parsers, `apply_move_impl`) specify `Some/None` precisely with proof obligations.
3. Invariants:

   * Pieces only on dark squares.
   * Counts never exceed 12 per side; only Men promote to Kings; no demotion.
4. Enumerations:

   * `enum_pos` complete with `NoDup` and cardinality 32.
5. Movement:

   * No flying kings; Men cannot move or capture backward.
6. Captures:

   * Mandatory capture and mandatory continuation; chain maximality or promotion termination enforced.
   * Captured pieces are removed **after** the chain, remain as blockers during the chain.
   * No jumping the same enemy piece twice.
7. Legality forbids steps if any capture exists for the moving side.
8. Promotion:

   * Immediate upon landing on crown-head; chain ends for Men.
9. Game state:

   * Forty-Move Rule counter counts **plies** since last capture **or** any man forward step by the mover; draw claim available at ≥ 80.
   * Threefold repetition detected via `(board, turn)` keys.
10. Terminal outcomes:

    * Elimination and immobilization produce a win for the opponent of the side to move.
    * Draws by agreement, threefold repetition, and Forty-Move Rule are supported (claim-based).
11. Generators:

    * Jumps generator yields only **maximal** chains (except when promotion ends them).
    * Steps generator suppressed whenever a jump exists.

---

### Notes for the implementer

* **Directionality (`forward_of`)** should be fixed by your coordinate convention:

  * If ranks increase from the Dark back rank (near squares 1–4) toward Light’s back rank (29–32), then `forward_of Dark r1 r2 := r2 = r1 + 1` (up the board) and `forward_of Light r1 r2 := r2 = r1 - 1`.
* **Transient occupancy during jump chains**: implement `simulate_jump_link` that updates an *ephemeral* set of captured enemy squares kept as “blocked” until the chain ends; the actual `board` is only updated once at the end.
* **Repetition keys**: do **not** include the `ply_without_capture_or_man_advance` counter in the key; threefold compares board placement and side to move only.
* **PDN I/O**: parsing numeric 1–32 is straightforward with your `pos_of_index`. For jumps, remember PDN lists only landings (e.g., `12x19x26`); you must reconstruct the `over` squares using geometry.
