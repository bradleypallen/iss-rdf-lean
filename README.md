# ISRDF — Lean 4 formalization of "Implication-Space Semantics for RDF"

Formalizes B. P. Allen, *Implication-Space Semantics for RDF* (draft, 6 Sept 2026),
in Lean 4 (v4.34.0-rc2) against Mathlib master (Sept 2026). Both files compile with
no `sorry`; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

Build: `lake update && lake exe cache get && lake build`.

## Where each result lives

| Note | Lean | File |
|---|---|---|
| Def 1–2 (terms, triples, graphs, instances) | `Term`, `Triple`, `Graph`, `Graph.inst` | Rdf.lean |
| Def 3 (simple entailment) | `SimpleEntails` | Rdf.lean |
| Lemma 1 (Conservativity) | `simpleEntails_iff_std` | Rdf.lean |
| Def 4 (regime, closure, R-entailment) | `Regime`, `Cl`, `Regime.clPos`, `Regime.Inconsistent`, `Regime.Entails` | Rdf.lean |
| Lemma 6 (uniformity of closure) | `Regime.cl_map`, `Regime.clPos_map`, `Regime.inconsistent_map`, `Regime.terms_clPos_subset`, `Regime.bnodes_clPos_subset` | Rdf.lean |
| Def 5–6 (implication space, RSR, roles, ⊔, ⊓, ∇) | `ISpace`, `RSR`, `Role`, `adj`, `adjFam`, `powSymj` | Semantics.lean |
| Lemma 2 (Reduction) | `reduction` | Semantics.lean |
| well-definedness of ⊔, ⊓ on roles | `RSR_adj`, `RSR_union`, `adj_congr` | Semantics.lean |
| Def 7 (content entailment, models) | `CEnt`, `Model`, `Model.SentEnt`, `Model.GEnt` | Semantics.lean |
| Prop 1 (Positional criterion) | `Model.positional` | Semantics.lean |
| Def 8 (canonical frame) | `IC` | Semantics.lean |
| Def 9 (triples as bearers) | `Model.br`, `Model.brG` | Semantics.lean |
| Def 10–11 (contents of graphs) | `Model.groundPos/groundNeg`, `Model.pos/neg` | Semantics.lean |
| Lemma 3 (Shapes) | `Model.mem_pos_iff`, `Model.mem_neg_iff`, `Model.mem_pairs_iff` | Semantics.lean |
| Def 12 (admissible fragment) | `Admissible` | Semantics.lean |
| Def 13 (base, fitness, B_C, B_R) | `Base`, `Model.Fit`, `canonicalBase`, `Regime.base` | Semantics.lean |
| B_R structural (monotone, Cut, explosive) | `Regime.base_mono_left/right`, `Regime.base_cut`, `Regime.base_explosive` | Semantics.lean |
| Def 14–15 (induced frame, Herbrand model) | `Base.frame`, `Base.herbrand`, `Base.herbrand_fit` | Semantics.lean |
| **Theorem 1 (Recovery)** | `recovery` | Semantics.lean |
| Lemma 4 (Witness coordinate) | `witness_coordinate` | Semantics.lean |
| Lemma 5 (Skolemization) | `skolemization`, `skolemInv` | Semantics.lean |
| **Lemma 7 (Witness characterization)** | `witness_characterization` | Semantics.lean |
| **Prop 2 (Incoherence recovery)** | `incoherence_recovery` | Semantics.lean |
| **Theorem 2 (Closure regimes)** | `closure_regimes`, `fitEnt_independent_of_N` | Semantics.lean |
| Corollary 1 (Simple RDF entailment) | `simple_entailment_recovery`, `simple_entailment_recovery_std` | Semantics.lean |

Not formalized: Corollaries 2–3 (RDFS, OWL 2 RL). They are instantiations of Theorem 2
at concrete rule tables and would require encoding those tables (and, for Cor. 2, the
appeal to Hayes & Patel-Schneider App. A / ter Horst Thm 4.12, which is external).

## Modelling decisions that differ from the note

* **Finiteness dropped.** Graphs are `Set`s and `N` is any set of names. No proof needs
  finiteness; the note uses it only so that the role operations are finitary.
* **Closure as an inductive predicate.** `Cl R X c` with `c : Option Triple`; `none` is ⊥.
  `Regime.clPos` is `cl_R(X) \ {⊥}`. Regimes are arbitrary sets of rules with range
  restriction and uniformity as structure fields (no schemas / decidability).
* **Roles via generating sets.** A "role" is carried by a generating set `H ⊆ S`;
  `Role I H` is the class of generating sets with the same `RSR`. Lemma 2 (`reduction`)
  justifies checking entailment on generating sets; `RSR_adj`/`RSR_union` show the
  operations respect the equivalence. Definition 10's ground contents are entered by
  their generating pairs (`groundPos`, `groundNeg`), which the note states immediately
  after Def 10; Def 11 is built from these with `powSymj`/`adjFam`, and Lemma 3 is proved.
* **Two entailment notions**, as in the note but made explicit: `Model.SentEnt Γ Δ`
  (Def 7 on *sets of atomic sentences*; what fitness quantifies over; Prop 1 applies) and
  `Model.GEnt N G H` (Def 10/11 graph contents; what Theorems 1–2 are about). The
  difference matters: `⟦H⟧⁻` is a power-symjunction, so `GEnt` for a ground `H` checks
  every non-empty `S ⊆ B(H)`, whereas `SentEnt` checks only `⟨B Γ, B Δ⟩`.
* **Herbrand model.** `Obj := Term`, interpretation the identity, so the bearer map is
  the identity and Def 14's frame is stated directly over ground triples.
* **Theorem 1 hypotheses.** `recovery` needs only `names(G) ⊆ N` and `names(H) ⊆ N`,
  not full admissibility — Skolemization is only used from Lemma 5 onward.
* `Model.Incoherent` (Prop 2) is `CEnt` against the generating set `{⟨∅,∅⟩}`, which is
  `adjFam` over the empty family (`adjFam_empty`).
