# Lean 4 formalization of implication-space semantics for RDF

Formalizes B. P. Allen, *Implication-Space Semantics for RDF* (draft, 30 September 2026),
in Lean 4 (v4.34.0) against Mathlib commit `5ed2965` (tag `v4.34.0`, Sept 2026). All eleven files compile with
no `sorry`; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

Build: `lake exe cache get && lake build`. `lakefile.toml` and `lake-manifest.json` both pin
Mathlib to commit `5ed2965`; do not run `lake update`, which would move Mathlib and break
lemma names.

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
| well-definedness of ⊓ and of binary ⊔ in its left argument (not yet shown for family ⊔ `adjFam` or ∇ `powSymj`) | `RSR_adj`, `RSR_union`, `adj_congr` | Semantics.lean |
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
| Renaming of a graph over `V` | `Renames`, `Renames.of_terms_subset` | General.lean, Entries.lean |
| Base given by `Cons` and incoherence (Containment, no new terms, invariance under renamings; prime by construction) | `ConsBase`, `ConsBase.base`, `ConsBase.mem_frame_iff` | General.lean |
| Lemma 5 (Skolemization), with both round trips | `SkolemPair`, `exists_skolemPair` | General.lean |
| Lemma 4 (Witness coordinate), for any `X` over the terms of `G` and `V` | `witness_coordinate'` | General.lean |
| General theorem in the Herbrand model (counterpart of Lemma 7; needs `N` nonempty) | `ConsBase.witness_characterization` | General.lean |
| **General theorem, part (P)** (counterpart of Prop 2) | `ConsBase.incoherent_iff_inc` | General.lean |
| **General theorem, part (T)** | `ConsBase.general` | General.lean |
| **General theorem, part (I)** | `ConsBase.general_independent`, `ConsBase.incoherent_independent` | General.lean |
| Regime base without explosion; agreement with Theorem 2 on `R`-consistent graphs | `Regime.consBase`, `Regime.fitEnt_skolem_iff` | General.lean |
| Lemma 6 with equality, for renamings | `Regime.mapT_clPos`, `Regime.renames_clPos` | Entries.lean |
| One round of defaults over a regime (abstract) | `DefaultStep`, `DefaultStep.empty`, `Regime.consBaseOf`, `Regime.consBaseOf_empty_cons`, `Regime.consBaseOf_empty_inc` | Entries.lean |
| Entries `⟨A, c; E⟩`, application, `D*`, incompatibility | `Entry`, `Entry.Applies`, `Entries`, `Entries.dstar`, `Entries.Incompat`, `Entries.applies_map`, `Entries.step` | Entries.lean |
| **Lemma A** (the entries base satisfies the hypotheses of the general theorem) | `Regime.entriesBase`, `Regime.entriesBase_cons`, `Regime.entriesBase_inc` | Entries.lean |
| General theorem at the entries base, parts (T) and (P) | `Regime.entries_general`, `Regime.entries_incoherent_iff` | Entries.lean |
| **Property 1 (Defeat witness)** | `Regime.defeat_witness` | Entries.lean |
| **Property 2 (Materialization)** | `Regime.consBaseOf_cons_union`, `Regime.consBaseOf_inc_union`, `Regime.clPos_union_of_subset`, `Regime.inconsistent_union_iff` | Entries.lean |
| **Property 1, counterpart for incoherence (Lost incoherence)** | `Regime.incoherence_witness` | Entries.lean |
| Two-variable entry schemas `X p Y \|~ c unless d₁, …` and their ground instances as an `Entries` | `Slot`, `Schema`, `Schema.Over`, `Schema.inst`, `schemaEntries`, `schemaBase`, `mem_cons_schema` | Examples.lean |
| Example 1: the entry set `X p Y \|~ X q X unless X p X` | `s0`, `E0`, `E0base`, `mem_cons_E0` | Examples.lean |
| **Example 1a (Nonmonotone)** | `E0_nonmonotone` | Examples.lean |
| **Example 1b (Definition 11 against the Skolem reading)** | `E0_def11_vs_skolem`, `E0_skolem_side`, `E0_def11_side_fails` | Examples.lean |
| Example 1b, hypotheses satisfiable; one closed instance | `E0_admissible`, `E0_def11_vs_skolem_exists`, `E0_instance_nat` | Examples.lean |
| **Example 3 (Cautious Monotony fails)**, entry `X p Y \|~ X q Y unless X q X` | `cautious_monotony_fails`, `cautious_monotony_fails_rel` | Examples.lean |
| **Example 3 (Cut fails)**, entries `X p Y \|~ X q Y`, `X q Y \|~ X r Y` | `cut_fails`, `cut_fails_rel` | Examples.lean |
| Single conclusions: the base relation is membership in `Cons` | `rel_singleton` | Examples.lean |
| **Example 2 (Redundant blank-node triples are not inert)**, entry `X p Y \|~ Y q Y unless Y p Y` | `redundant_bnode_not_inert`, `sInert`, `InertBase`, `mem_cons_Inert` | Examples.lean |
| Pattern terms, triple patterns, instantiation | `PTerm`, `PTerm.eval`, `PTerm.Const`, `PTriple`, `PGraph`, `PGraph.inst`, `PGraph.vars`, `PGraph.Over`, `PGraph.mapT_inst`, `PGraph.inst_congr` | Patterns.lean |
| Pattern entries `⟨A, c; E⟩` with a guard; ground instances; well-formedness | `PEntry`, `PEntry.inst`, `PEntry.WF`, `ConclOK`, `PEntry.applies_inst_iff` | Patterns.lean |
| **Pattern entries form an `Entries`** | `patternEntries`, `mem_patternEntries` | Patterns.lean |
| Invariant guards: closure under ∧, ∨, projection; literal comparisons; literal view; `X ≠ Y`; `X ≠ k` | `GuardInvariant`, `projGuard`, `GuardInvariant.and`, `GuardInvariant.or`, `GuardInvariant.mono`, `GuardInvariant.proj`, `litGuard`, `guardInvariant_lit`, `Term.litView`, `guardInvariant_litView`, `neGuard`, `guardInvariant_ne`, `neConstGuard`, `guardInvariant_neConst` | Patterns.lean |
| A blank-node test is not an invariant guard | `not_guardInvariant_isBnode` | Patterns.lean |
| **Pattern rules form a `Regime`** | `PRule`, `PRule.inst`, `PRule.WF`, `patternRegime` | Patterns.lean |
| Entries base over the empty regime | `emptyRegime_entriesBase_cons`, `emptyRegime_entriesBase_inc` | Patterns.lean |
| Shape (a): incompatibility with several defeaters; lost incoherence | `Shapes.typeEntry`, `Shapes.typeEntry_wf`, `Shapes.type_incoherence_lost` | Patterns.lean |
| Shape (b): defeater with an existential variable; a concrete defeat | `Shapes.excEntry`, `Shapes.excEntry_wf`, `Shapes.exc_defeat` | Patterns.lean |
| Shape (c): several premises with a literal guard | `Shapes.contempEntry`, `Shapes.contempEntry_wf`, `Shapes.contemp_inc_iff` | Patterns.lean |
| The case-study regime (two rules) and its base | `Shapes.subTransRule`, `Shapes.instUpRule`, `Shapes.caseRegime`, `Shapes.caseBase` | Patterns.lean |
| A ground antecedent is one pair (Definition 11 reduces to Definition 10) | `Admissible.inst_ground`, `Model.biUnion_inst_of_ground`, `Model.gEnt_ground_iff`, `Model.incoherent_ground_iff` | Bridge.lean |
| Definition 11 gives the Skolem reading, in every model and for every base | `Model.gEnt_inst_of_gEnt`, `Model.incoherent_inst_of_incoherent`, `fitEnt_inst_of_fitEnt` | Bridge.lean |
| Base given by `Cons` and incoherence, with an explosion flag `e`; `e := False` is `ConsBase.base` | `ConsBase.baseWith`, `ConsBase.baseWith_false`, `ConsBase.mem_frame_with_iff`, `Base.ext_rel` | Bridge.lean |
| **General theorem with or without explosion**, parts (T) and (P) and the Herbrand form (needs `e ∨ N.Nonempty`) | `ConsBase.general_with`, `ConsBase.incoherent_iff_inc_with`, `ConsBase.witness_characterization_with` | Bridge.lean |
| The `General.lean` results as the case `e := False` | `ConsBase.general_of_with`, `ConsBase.incoherent_iff_inc_of_with`, `ConsBase.witness_characterization_of_with` | Bridge.lean |
| Base monotone and invariant under instance mappings | `ConsBase.InstMonotone`, `Regime.consBase_instMonotone` | Bridge.lean |
| "If" halves of Lemma 7 and Prop 2 on such a base (no Skolemization, no condition on `N`) | `ConsBase.InstMonotone.gEnt_of_cons`, `ConsBase.InstMonotone.incoherent_of_inc` | Bridge.lean |
| **The bridge**: on such a base, Definition 11 and the Skolem reading of the antecedent agree | `ConsBase.InstMonotone.gEnt_iff_skolem`, `ConsBase.InstMonotone.incoherent_iff_skolem`, `ConsBase.InstMonotone.fitEnt_iff_skolem` | Bridge.lean |
| General theorem with Definition 11 in antecedent position, on such a base | `ConsBase.InstMonotone.general_def11`, `ConsBase.InstMonotone.incoherent_def11` | Bridge.lean |
| `B_R` is the exploding base of `cl_R` and `R`-inconsistency; the bridge over `B_R` on every graph (no consistency hypothesis) | `Regime.base_eq_baseWith`, `Regime.fitEnt_iff_skolem` | Bridge.lean |
| **Theorem 2 and Prop 2 re-derived from the general theorem** (same statements; proofs do not use Lemma 7, Prop 2, Lemma 4 or Lemma 5 of Semantics.lean) | `closure_regimes_of_general`, `incoherence_recovery_of_general` | Bridge.lean |
| Lemmas 4 and 5 as special cases of their General.lean forms | `witness_coordinate_of_general`, `skolemization_of_skolemPair` | Bridge.lean |
| Defeasible modus ponens; a default conclusion is withdrawn only by a listed defeater; `Cons` is closed under the regime | `StandardPatterns.dmp`, `StandardPatterns.persists`, `StandardPatterns.persists_of_no_defeaters`, `StandardPatterns.not_applies_of_defeater`, `StandardPatterns.cons_closed`, `StandardPatterns.cons_rule`, `StandardPatterns.rel_singleton_iff` | StandardPatterns.lean |
| Class defaults and clashes over the empty regime, with `Cons` and incoherence computed | `StandardPatterns.Spec`, `StandardPatterns.Spec.base`, `StandardPatterns.mem_cons_iff`, `StandardPatterns.inc_iff` | StandardPatterns.lean |
| **The standard patterns** (Pelletier and Asher 1997, section 3.1) as closed instances: defeasible modus ponens and its defeat, Nixon diamond and its extension, Penguin and Weak Penguin, the two independence patterns | `StandardPatterns.c1_dmp`, `c2_conflict_located`, `c2_listed_defeater`, `c3_nixon`, `c4_no_chaining`, `c5_penguin_no_specificity`, `c5_penguin_listed`, `c5_weak_penguin`, `c6_fido`, `c7_charlie`, `c7_charlie_incoherent` | StandardPatterns.lean |
| Right Weakening from ⊥ and Cautious Monotony carry incoherence to every extension by a consequence (abstract form, formulas, sets) | `NotCumulative.bot_persists`, `NotCumulative.klm_false_persists`, `NotCumulative.incoherence_persists`, `NotCumulative.incoherence_persists_list`, `NotCumulative.not_both_of_lost_incoherence` | NotCumulative.lean |
| **A base with lost incoherence is not cumulative**; which rule fails with explosion and which without | `NotCumulative.not_cumulative`, `NotCumulative.explosion_rwBot`, `NotCumulative.explosion_cm_fails`, `NotCumulative.no_explosion_dichotomy`, `NotCumulative.coherent_not_subset_closed` | NotCumulative.lean |
| The same at shape (a): with explosion Cautious Monotony fails; without it Right Weakening from ⊥ fails and Cautious Monotony holds | `NotCumulative.typeBase_not_cumulative`, `NotCumulative.typeBase_explosion_cm_fails`, `NotCumulative.typeBase_no_explosion_rw_fails`, `NotCumulative.typeBase_no_explosion_cm_holds` | NotCumulative.lean |
| The regime `R_O = R ∪ {⟨∅, t⟩ : t ∈ O}` for an ontology `O` all of whose terms are IRIs, as a regime over `V` and the IRIs of `O`; its closure of `X` is the closure under `R` of `X ∪ O` | `Graph.iris`, `Graph.IriOnly`, `Regime.withOntology`, `Regime.cl_withOntology`, `Regime.clPos_withOntology`, `Regime.inconsistent_withOntology` | OntologyRelative.lean |
| **Corollary (Ontology-relative regimes)**, for an ontology without literals, from Theorem 2; its counterpart for incoherence, from Prop 2 | `Regime.ontology_relative`, `Regime.ontology_relative_incoherent` | OntologyRelative.lean |
| The rules (2) to (7) of ρdf (Muñoz, Pérez and Gutierrez 2009, Table 1) as 23 pattern rules, each well-formed; none concludes ⊥ | `RhoDf.Vocab`, `RhoDf.Vocab.In`, `RhoDf.RuleId`, `RhoDf.rule`, `RhoDf.rule_wf`, `RhoDf.rule_concl_ne_none`, `RhoDf.patternRegime_not_inconsistent` | RhoDf.lean |
| **The ρdf rules form a `Regime`**: rules (2) to (7), and rules (2), (3) and (4) alone; no graph is inconsistent under either | `RhoDf.rhoRegime`, `RhoDf.mrdfRegime`, `RhoDf.rho_not_inconsistent`, `RhoDf.mrdf_not_inconsistent` | RhoDf.lean |
| **Theorem 2 for the ρdf rules**, and the same with a schema held fixed, by the ontology-relative corollary | `RhoDf.rho_recovery`, `RhoDf.mrdf_recovery`, `RhoDf.rho_ontology_recovery`, `RhoDf.mrdf_ontology_recovery` | RhoDf.lean |
| Two checks that the transcribed rules fire: rule (3b), and rule (2b) with a variable as predicate | `RhoDf.mrdf_sc_type`, `RhoDf.mrdf_sp_inherit` | RhoDf.lean |

Not formalized: Corollaries 2–3 (RDFS, OWL 2 RL). They are instantiations of Theorem 2
at concrete rule tables and would require encoding those tables (and, for Cor. 2, the
appeal to Hayes & Patel-Schneider App. A / ter Horst Thm 4.12, which is external).
`RhoDf.lean` encodes one such table, that of ρdf. It shows that the rules as transcribed
form a regime. It does not check the transcription against the paper's table, and it does
not formalize that paper's theorems relating the rules to RDFS entailment. The paper
instantiates a rule only where every triple is well formed; the library takes every
instance over generalized triples.

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
