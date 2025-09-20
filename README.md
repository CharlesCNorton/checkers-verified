# Formal Specification of English Draughts in Coq

## Abstract

This repository contains a complete formalization of English Draughts (8×8 Checkers) in the Coq proof assistant, comprising approximately 4,300 lines of formally verified code. The implementation provides machine-checked proofs of correctness for all game mechanics, including complex rules such as multi-jump capture chains, mandatory capture enforcement, and the promotion exception that terminates capture sequences. To our knowledge, this represents the first complete formalization of a traditional two-player board game in Coq with full ruleset verification.

## Introduction

The formalization follows a comprehensive specification document that codifies the complete Laws of Checkers in 21 sections, from fundamental board geometry through metatheorems about game tree properties. The implementation achieves both soundness and completeness: every legal move according to the official rules is generated, and every generated move is proven legal.

The project addresses several technical challenges inherent in formalizing board games: managing transient board states during capture chains where captured pieces remain as blocking obstacles until chain completion, implementing the forcing rule that makes captures mandatory when available, and correctly handling the edge case where promotion to King terminates a capture sequence even when additional captures would be available.

## Technical Approach

The formalization employs dependent types to enforce invariants at the type level. Positions are restricted to the 32 dark squares through a proof-carrying record type, eliminating an entire class of potential errors. The board is represented as a total function from positions to optional pieces, with extensional equality enabling reasoning about board transformations.

Movement geometry is formalized through precise diagonal relations, distinguishing between adjacency (distance 1) and jump relations (distance 2). The implementation correctly enforces directional constraints: men may only move and capture forward, while kings move omnidirectionally. Chain validity is verified relative to transient board states, ensuring captured pieces cannot be jumped twice and properly block subsequent jumps until removed.

The game state maintains a repetition book using multiset semantics for threefold repetition detection and tracks plies since the last capture or man advance for the forty-move rule. The specification distinguishes carefully between moves that reset this counter (captures and forward moves by men) and those that increment it, following Article 17 of the Laws precisely.

## Validation

Correctness is established through multiple validation strategies. Perft (performance test) values are verified through depth 6, matching established references for the starting position. The move generation algorithm is proven complete with respect to the legal move specification. State transitions preserve well-formedness invariants, and the apply_move function is shown to be deterministic.

The implementation includes a verified game transcript demonstrating legal play from opening through endgame, with each move verified by Coq's kernel. This provides concrete evidence that the formalization captures actual checkers gameplay correctly.

## Repository Structure

The implementation is organized into three main files. The specification document (`checkers_laws.md`) provides the complete ruleset in formal legal language. The formalization (`checkers_formal_spec.v`) contains the mathematical specification with validation requirements. The implementation (`checkers_coq.v`) provides the complete Coq formalization with all proofs.

The code is structured in 22 sections following the specification, progressing from foundations through finite domain theory, position abstraction, game ontology, movement rules, capture chains, forcing rules, state representation, move generation, terminal conditions, and validation theorems. A final section demonstrates a complete verified game.

## Installation and Usage

The formalization requires Coq 8.10 or later. To verify the implementation:

```bash
coqc checkers_coq.v
```

To explore specific theorems interactively, load the file in CoqIDE or Proof General. The perft validation examples can be uncommented for additional verification, though higher depths require significant computation time.

## Related Work

While puzzle games such as Sudoku and Sokoban have been formalized in Coq, and partial chess implementations exist focusing on specific endgames, this project provides the first complete formalization of a traditional board game. The approach builds on established techniques from the Coq community, particularly the use of finite types from Mathematical Components and decidability proofs for game predicates.

## Citation

If you use this formalization in academic work, please cite:

```
[Charles Norton]. (2025). Formal Specification of English Draughts in Coq.
https://github.com/CharlesCNorton/checkers-verified/
```
