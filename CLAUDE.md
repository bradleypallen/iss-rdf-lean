# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

Two artifacts that must stay in sync:

* `manuscript.tex` — B. P. Allen, *Implication-Space Semantics for RDF* (draft, 6 Sept 2026), with `references.bib`.
* `ISRDF/` — a Lean 4 formalization of that manuscript's numbered Definitions, Lemmas, Theorems, Propositions and Corollaries.

Every Lean declaration is docstring-tagged with the manuscript item it formalizes
(`/-- Definition 5: ... -/`, `/-- **Theorem 1 (Recovery).** ... -/`). `README.md` holds the
authoritative note→Lean cross-reference table. **When a definition or a statement changes on
either side, update the other side and the README table.**

Only source is tracked: `.lake/` (8.4 GB of Mathlib oleans), the LaTeX aux files, and
`manuscript.pdf` are all gitignored, so a fresh clone needs `lake exe cache get && lake build`
and `latexmk -pdf manuscript.tex` to reproduce them.

## Build and check

```sh
lake exe cache get          # fetch prebuilt Mathlib oleans (do this before the first build)
lake build                  # build both modules
lake build ISRDF.Semantics  # build a single module
lake env lean ISRDF/Rdf.lean   # type-check one file directly, full error output
```

`lakefile.toml` and `lake-manifest.json` both pin Mathlib to commit `a2ba36b` (Sept 2026),
and `lean-toolchain` pins `v4.34.0-rc2`. Do **not** run `lake update` unless deliberately
bumping Mathlib: change the `rev` in `lakefile.toml` first, and expect the update to
invalidate the Mathlib cache and break lemma names.

There is no test suite. The two checks that stand in for one:

```sh
grep -rn 'sorry' ISRDF/                       # must return nothing
printf 'import ISRDF\n#print axioms ISRDF.recovery\n' | lake env lean --stdin
```

The main theorems (`recovery`, `witness_characterization`, `incoherence_recovery`,
`closure_regimes`, `simple_entailment_recovery`) must depend only on
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

`ISRDF.lean` is a bare re-export. Real content is two modules, layered:

**`ISRDF/Rdf.lean` (§2) — syntax and entailment regimes.** `Term`/`Triple`/`Graph` over three
abstract carrier types `Iri Lit Bn` (never instantiated; every result is parametric in them).
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

## Conventions in the Lean sources

* `set_option autoImplicit false` at the top of both files — declare every variable.
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
