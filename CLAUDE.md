# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

Two artifacts that must stay in sync:

* `manuscript.tex` — B. P. Allen, *Implication-Space Semantics for RDF* (draft, 30 September 2026), with `references.bib`.
* `ISRDF/` — a Lean 4 formalization of that manuscript's numbered Definitions, Lemmas, Theorems, Propositions and Corollaries
  (`Rdf.lean`, `Semantics.lean`), plus a nonmonotone extension
  (`General.lean`, `Entries.lean`, `Examples.lean`, `Patterns.lean`) and a module that
  joins the two proof chains (`Bridge.lean`).

Every Lean declaration is docstring-tagged with the manuscript item it formalizes
(`/-- Definition 5: ... -/`, `/-- **Theorem 1 (Recovery).** ... -/`). `README.md` holds the
authoritative note→Lean cross-reference table. **When a definition or a statement changes on
either side, update the other side and the README table.**

The nonmonotone extension is ahead of the manuscript: its items (the general theorem,
Lemma A, Properties 1 and 2, the examples) have **no manuscript numbers yet** and are tagged
by name in the docstrings and in the README table. When the manuscript gains those items,
replace the names with numbers on both sides. `Claude outputs/handoff/` holds the working
notes for that extension (`HANDOFF.md`, `RESULT.md`, check logs); it is not part of either
artifact.

Only source is tracked: `.lake/` (8.4 GB of Mathlib oleans), the LaTeX aux files, and
`manuscript.pdf` are all gitignored, so a fresh clone needs `lake exe cache get && lake build`
and `latexmk -pdf manuscript.tex` to reproduce them.

## Build and check

```sh
lake exe cache get          # fetch prebuilt Mathlib oleans (do this before the first build)
lake build                  # build all seven modules
lake build ISRDF.Semantics  # build a single module
lake env lean ISRDF/Rdf.lean   # type-check one file directly, full error output
```

`lakefile.toml` and `lake-manifest.json` both pin Mathlib to commit `5ed2965` (tag `v4.34.0`,
Sept 2026), and `lean-toolchain` pins `v4.34.0`. (Do not go back to `v4.34.0-rc2`: its `lake`
crashes on macOS 27, leanprover/lean4#15087.) Do **not** run `lake update` unless deliberately
bumping Mathlib: change the `rev` in `lakefile.toml` first, and expect the update to
invalidate the Mathlib cache and break lemma names.

There is no test suite. The two checks that stand in for one:

```sh
grep -rn 'sorry' ISRDF/                       # must return nothing
printf 'import ISRDF\n#print axioms ISRDF.recovery\n' | lake env lean --stdin
```

The main theorems (`recovery`, `witness_characterization`, `incoherence_recovery`,
`closure_regimes`, `simple_entailment_recovery`, and in the extension `ConsBase.general`,
`ConsBase.incoherent_iff_inc`, `Regime.entries_general`, `Regime.defeat_witness`,
`Regime.incoherence_witness`, `Regime.consBaseOf_cons_union`, and in `Bridge.lean`
`ConsBase.general_with`, `ConsBase.InstMonotone.fitEnt_iff_skolem`,
`closure_regimes_of_general`, `incoherence_recovery_of_general`) must depend only on
`propext, Classical.choice, Quot.sound`. `Classical.choice` enters through Mathlib's set
lemmas (`recovery` and `Model.positional` depend on it without using Skolemization) as well
as through `skolemInv` (Lemma 5), which is `noncomputable` by construction.

Manuscript: `latexmk -pdf manuscript.tex`.

`manuscript.log` is ISO-8859 encoded, not UTF-8. macOS `grep` therefore classifies it as
binary and prints *nothing at all* rather than reporting matches — a check for errors will
come back falsely clean. Always pass `-a` when reading it:

```sh
grep -an '^!' manuscript.log                       # errors
grep -an 'undefined\|Undefined' manuscript.log     # unresolved refs and citations
grep -an 'LaTeX Warning\|Package .* Warning' manuscript.log
grep -ac 'Overfull \\hbox' manuscript.log          # cosmetic; a few are expected
```

## Architecture

`ISRDF.lean` is a bare re-export of seven modules. The manuscript's content is two of them,
layered; the nonmonotone extension (below) is four more on top; `Bridge.lean` (last
subsection) joins the two proof chains:

**`ISRDF/Rdf.lean` (§2) — syntax and entailment regimes.** `Term`/`Triple`/`Graph` over three
abstract carrier types `Iri Lit Bn` (every result is parametric in them; the only
instantiation anywhere is the closed example `Examples.E0_instance_nat`).
`Graph` is `Set (Triple (Term ..))`. Instance mappings are *total* `Bn → Term`, applied via
`Graph.inst`; `Graph.mapT` is the more general pointwise map used for regime uniformity.
`Regime` bundles a rule set with its range-restriction and uniformity proofs as structure
fields. Closure is the inductive predicate `Cl R X : Option Triple → Prop`, where `none` is
`⊥`; `Regime.clPos` is the `⊥`-free part and `Regime.Inconsistent` is `Cl R X none`.

**`ISRDF/Semantics.lean` (§3) — implication-space semantics and the recovery results.**
Built on `ISpace Br := Set Br × Set Br` with `RSR`, `Role`, `adj`, `adjFam`, `powSymj`.
A `Model` supplies `Obj`, a good-implication set `I`, and `interp : Term → Obj`; the bearer
map `Model.br` is `Triple.map interp`.

Three structural points that are easy to get wrong when editing:

1. **Roles are handled by generating sets, not quotients.** `Role I H` is the class of sets
   with the same `RSR`. Lemma 2 (`reduction`) is what licenses checking entailment on a
   generating set; `RSR_adj`/`RSR_union`/`adj_congr` are what make the operations
   well-defined on the equivalence. Any new role operation needs the same treatment.
2. **Two distinct entailment notions, deliberately.** `Model.SentEnt Γ Δ` (Def 7, sets of
   atomic sentences) is what `Model.Fit` quantifies over and what `Model.positional`
   (Prop 1) collapses to a single membership `(brG Γ, brG Δ) ∈ M.I`. `Model.GEnt N G H`
   (Def 10/11 graph contents) is what Theorems 1–2 are about, and it is strictly more
   demanding: `⟦H⟧⁻` is a power-symjunction, so it ranges over every non-empty
   `S ⊆ B(H)` and every instance map. Do not conflate them.
3. **The Herbrand model is `Obj := Term` with `interp = id`**, so `Base.herbrand_br` and
   `Base.herbrand_brG` are `rfl`-level simp lemmas and Def 14's frame is stated directly
   over ground triples. Most proofs in §3.4–3.5 open by `rw [Model.gEnt_iff]` then
   `simp only [Base.herbrand_brG]`.

The proof spine: `recovery` (Thm 1) reduces fit-model entailment to the Herbrand model;
`witness_characterization` (Lemma 7) identifies Herbrand `GEnt` with `Regime.Entails`, using
`skolemization` (Lemma 5) and `witness_coordinate` (Lemma 4); `closure_regimes` (Thm 2) is
their composition; `simple_entailment_recovery` (Cor 1) instantiates it at `emptyRegime`.

### The nonmonotone extension

Four further modules, each importing the previous one. They add declarations only; nothing
in `Rdf.lean` or `Semantics.lean` was changed for them, and they should stay that way.

**`ISRDF/General.lean` — the general theorem.** `ConsBase` is a base given by a consequence
function `cons` and an incoherence predicate `inc`, assumed only to satisfy Containment, no
new terms, and invariance under renamings. `ConsBase.base` is the non-exploding base
(`Δ` meets `cons Γ`, or `Δ = ∅` and `inc Γ`). A graph in antecedent position is read through
its Skolemization `G.inst νsk`; `SkolemPair` packages Lemma 5 with both round trips.
`ConsBase.general` (part T), `ConsBase.incoherent_iff_inc` (part P) and
`ConsBase.general_independent` (part I) are the counterparts of Theorem 2, Proposition 2
and `fitEnt_independent_of_N`. The proof is `recovery` applied to the ground graph
`G.inst νsk`, then `ConsBase.witness_characterization`.

**`ISRDF/Entries.lean` — regimes with defeasible entries.** Two layers. Layer 1:
`DefaultStep` is one round of defaults as an arbitrary function `dstar` of the closure, and
`Regime.consBaseOf` turns a regime plus a step into a `ConsBase`
(`cons X = clPos (clPos X ∪ dstar (clPos X))`). Layer 2: `Entry` and `Entries` are ground
entries `⟨A, c; E⟩`; `Entries.step` is their `DefaultStep` and `Regime.entriesBase` is
Lemma A. Property 2 (`consBaseOf_cons_union`, `consBaseOf_inc_union`) is proved at layer 1;
Property 1 (`defeat_witness`) and its incoherence counterpart (`incoherence_witness`) at
layer 2.

**`ISRDF/Examples.lean` — examples and counterexamples**, in the namespace
`ISRDF.Examples`. `Schema` and `schemaEntries` turn two-variable entry patterns
`X p Y |~ c unless d₁, …` into an `Entries`. On top of that: a nonmonotone instance
(`E0_nonmonotone`), Definition 11 against the Skolem reading (`E0_def11_vs_skolem`), the
failures of Cautious Monotony and Cut (`cautious_monotony_fails`, `cut_fails`), and
redundant blank-node triples not being inert (`redundant_bnode_not_inert`). The schema
layer here is a special case of the pattern layer in `Patterns.lean`; it is kept because
the examples are stated on it.

**`ISRDF/Patterns.lean` — pattern entries and pattern rules.** `PTerm` is a variable, an
IRI constant or a literal constant; `PEntry` has any number of premise patterns, an
optional conclusion, defeater patterns that may use variables not in the premises (read
existentially), and a guard on substitutions. `patternEntries` proves that the ground
instances of well-formed pattern entries (`PEntry.WF`) form an `Entries`, and
`patternRegime` that the ground instances of well-formed pattern rules form a `Regime`.
`PEntry.applies_inst_iff` says when an instance fires: premises matched in `K`, and no
defeater matched in `K` by an extension of the premise bindings. The namespace
`ISRDF.Shapes` instantiates the layer at the shapes of the Wikidata case study
(`typeEntry`, `excEntry`, `contempEntry`, `caseRegime`, `caseBase`).

Structural points for the extension:

4. **Invariance is under renamings, not under arbitrary maps fixing `L ∪ V`.**
   `Renames V ρ X` says `ρ` is undone on the terms of `X` by another map fixing `L ∪ V`.
   `Regime.uniform` closes under all such maps, which is right for rules and wrong for
   entries: defeat is not preserved by maps that merge terms. For the same reason
   `Regime.mapT_clPos` (equality) needs `Renames`, while `clPos_map` (inclusion) does not.
5. **`cons` is not assumed monotone, and `dstar` is not monotone.** In `cons_map` you cannot
   pass from `dstar (mapT ρ K)` to `dstar` of a superset; go through the equality
   `mapT_clPos`. Monotonicity lemmas (`clPos_mono`) apply to the closure only.
6. **`N.Nonempty` is a hypothesis of the general theorem** and has no counterpart in
   Theorem 2: without explosion, an empty `N` and a succedent with blank nodes leave the
   succedent family empty.
7. **Defaults are drawn in one pooled round.** Entries never see each other's conclusions,
   so `cons` is not idempotent and Cut fails even with no defeaters (`cut_fails`). Do not
   "fix" this by iterating `dstar`; it is the definition.
8. **Pattern well-formedness is four conditions, and guards are the delicate one.** IRI
   constants of premises and defeaters lie in `V`; each conclusion term occurs in the
   premises or is an IRI in `V`; the guard's projection onto the premise variables is
   `GuardInvariant`. A new guard form needs an invariance proof: comparisons of literal
   values and `X ≠ Y` on premise variables are invariant, a test for a blank node or for a
   particular IRI outside `V` is not (`not_guardInvariant_isBnode`). Pattern rules cannot
   carry `X ≠ Y` at all, because `Regime.uniform` closes under maps that merge terms.

### One spine for both cases

**`ISRDF/Bridge.lean` — the monotone case as a corollary of the general theorem.** Imports
`General.lean` only and adds declarations only. `Semantics.lean` proves Theorem 2 with
Definition 11 on both sides and explosion; `General.lean` proves the general theorem with
the Skolem reading of the antecedent and no explosion. This module makes one chain of them:

* `ConsBase.baseWith e` is the base of `cons` and `inc` with an explosion flag `e : Prop`.
  `e := False` is `ConsBase.base` (`baseWith_false`); `e := True` at a regime is `B_R`
  (`Regime.base_eq_baseWith`).
* `ConsBase.general_with`, `incoherent_iff_inc_with` and `witness_characterization_with`
  are the general theorem for `baseWith e`. The `General.lean` results are the case
  `e := False` (`general_of_with` and its two companions).
* `Model.gEnt_inst_of_gEnt` and `fitEnt_inst_of_fitEnt`: Definition 11 gives the Skolem
  reading in every model, with nothing assumed about the base. It rests on
  `Model.gEnt_ground_iff` (a ground antecedent is one pair).
* `ConsBase.InstMonotone` says `cons` and `inc` are monotone and preserved by every
  instance mapping. On such a base the two readings of the antecedent agree
  (`InstMonotone.gEnt_iff_skolem`, `fitEnt_iff_skolem`), which gives the general theorem
  with Definition 11 in antecedent position (`InstMonotone.general_def11`).
* `closure_regimes_of_general` and `incoherence_recovery_of_general` have the statements of
  `closure_regimes` and `incoherence_recovery` and are proved from the above
  (`Regime.consBase_instMonotone`). They do not use `witness_characterization`,
  `incoherence_recovery`, `witness_coordinate` or `skolemization` from `Semantics.lean`.

The spine: `recovery` (Thm 1) to reach the Herbrand model; the bridge to pass from
Definition 11 to the Skolemized antecedent; `witness_characterization_with` on the ground
antecedent. Without `InstMonotone` the bridge holds in one direction only, and
`Examples.E0_def11_vs_skolem` shows the other direction failing.

Structural points for the bridge:

9. **The hypothesis on `N` is `e ∨ N.Nonempty`.** With explosion `N` may be empty, which is
   why Theorem 2 has no such hypothesis (point 6); without it `N` must be nonempty.
10. **`InstMonotone` is strictly stronger than the `ConsBase` fields.** `cons_inst` and
    `inc_inst` are invariance under every substitution for blank nodes, including ones
    that merge terms; `ConsBase` assumes invariance under renamings only (point 4). An
    entries base in general does not satisfy `InstMonotone` (`Examples.E0_nonmonotone`).
    Do not add it as a `ConsBase` field.
11. **The originals stay.** `closure_regimes`, `incoherence_recovery` and Lemma 7 in
    `Semantics.lean` are not replaced by the re-derived versions; the two sets of proofs
    are kept side by side, and each new statement is definitionally the old one.

## Conventions in the Lean sources

* `set_option autoImplicit false` at the top of every file — declare every variable.
* Finiteness is dropped throughout: graphs and the name set `N` are arbitrary `Set`s. No
  proof needs finiteness. Do not reintroduce `Finset`.
* `Admissible N G H V` (Def 12) is the standing hypothesis for Lemma 7 onward, chiefly for
  its `skolem` field. `recovery` deliberately needs *less* — only `G.names ⊆ N` and
  `H.names ⊆ N` — because Skolemization is not used until Lemma 5. Keep it that way.
* Prefer following the existing style: explicit `rintro`/`obtain` destructuring,
  `simp only [...]` with named lemmas over bare `simp`, `calc` for subset chains.

## Known gaps

Corollaries 2–3 of the manuscript (RDFS, OWL 2 RL) are **not** formalized. They are
instantiations of Theorem 2 at concrete rule tables; formalizing them means encoding those
tables, and for Cor. 2 also depends on an external completeness result
(Hayes & Patel-Schneider App. A / ter Horst Thm 4.12).

In the nonmonotone extension, not formalized:

* Necessity of the pattern well-formedness conditions. `patternEntries` proves they are
  sufficient; that each is needed is argued on paper only.
* Guards on pattern rules.
* A fit-models version of part (P): `incoherent_iff_inc` is stated in the Herbrand model,
  as Proposition 2 is.
* `manuscript.tex` has no text yet for any item of the extension.
