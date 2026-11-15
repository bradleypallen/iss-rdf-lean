# Proof ledger: the general theorem, Lemma A and the properties

Prepared Sat 14 Nov 2026 by the Claude app session, from the uncommitted working tree of
`iss-rdf-lean` as it stood at about 17:00 UTC (six modules, `lake build` green, no `sorry`).

Purpose: raw material for the English proofs, which Brad writes. Each item gives the
statement in the paper's notation, the Lean name, every hypothesis with the step that uses
it, and the proof steps in order. Nothing here is paper prose.

Coverage: Part 1 (`General.lean`) and Part 2 (`Entries.lean`) are ledgered from a full
reading of the Lean. Part 3 (`Patterns.lean`, `Examples.lean`) is an inventory taken from
the Lean session's report; its proof steps are not ledgered yet.

## Notation

| Here | Meaning | Lean |
|---|---|---|
| L, V, N | literals; the regime's vocabulary (IRIs); the name set | `Lit`, `V`, `N` |
| terms(X) | terms occurring in X | `Graph.terms` |
| μ(H) | instance of H under μ : blank nodes → terms | `Graph.inst μ H` |
| ρ(X) | image of X under a term map ρ | `Graph.mapT ρ X` |
| IMap(N, H) | maps sending the blank nodes of H into N | `IMap N H` |
| Lex(N) | triples all of whose terms are in N | `Lex N` |
| X simply entails H | some μ has μ(H) ⊆ X (μ ranges over all terms) | `SimpleEntails X H` |
| ρ fixes L ∪ V | ρ(l) = l for literals, ρ(v) = v for v ∈ V | `FixesLV V ρ` |
| cl(X) | the ⊥-free closure cl_R(X) \ {⊥} | `R.clPos X` |
| G ⊨_B H | implication in all models fit for B (Def. 10/11 contents) | `FitEnt B G H` |
| H_B | the Herbrand model of B | `B.herbrand` |

"Unfolded Herbrand implication" below means `Model.gEnt_iff` after `Base.herbrand_brG`:
⟦G⟧ |~ ⟦H⟧ in H_B iff for every nonempty x ⊆ IMap(N, G) and every selection S (a nonempty
S(μ) ⊆ μ(H) for each μ ∈ IMap(N, H)), the pair ⟨⋃_{ν ∈ x} ν(G), ⋃_μ S(μ)⟩ is in the frame.

---

# Part 1. The general theorem (`ISRDF/General.lean`)

## D1. Renaming of a graph

`Renames V ρ X`: ρ fixes L ∪ V, and there is ρ′ fixing L ∪ V with ρ′(ρ(x)) = x for every
term x of X.

For the prose:
* It is relative to a graph. ρ need not be injective elsewhere.
* The inverse must itself fix L ∪ V. The pattern layer uses this (it is what makes "is a
  literal" invariant).
* Why not "permutation" or "injective map": the inverse σ of a Skolemization sends both the
  Skolem IRI sk(b) and the blank node b to b (`skolemInv`). It is a renaming of ν_sk(G)
  only.

## D2. A base presented by Cons and Inc

`ConsBase`: a function Cons on graphs and a predicate Inc on graphs with

* (C1) Containment: X ⊆ Cons(X). `extensive`
* (C2) No new terms: terms(Cons(X)) ⊆ terms(X) ∪ V. `terms_cons`
* (C3) If ρ is a renaming of X then ρ(Cons(X)) ⊆ Cons(ρ(X)). `cons_map`
* (C4) If ρ is a renaming of X and Inc(X) then Inc(ρ(X)). `inc_map`

For the prose:
* (C3) and (C4) are one-directional. The other direction is obtained by applying them to
  the inverse renaming.
* Nothing is assumed monotone. Nothing is assumed about Cons(Cons(X)).
* Cons and Inc are applied to graphs with whatever terms they have, blank nodes included,
  read as constants.

## D3. The base of a ConsBase

`ConsBase.base N`: Γ |~ Δ iff Δ ∩ Cons(Γ) ≠ ∅, or Δ = ∅ and Inc(Γ).

* It is a base in the sense of Definition 13: Containment follows from (C1) (if t ∈ Γ ∩ Δ
  then t ∈ Δ ∩ Cons(Γ)).
* Primeness is built in: for Δ ≠ ∅, Γ |~ Δ iff Γ |~ {t} for some t ∈ Δ.
* No explosion: an incoherent Γ implies ∅ and whatever is in Cons(Γ), nothing more.
* `ConsBase.mem_frame_iff`: for Γ, Δ ⊆ Lex(N), ⟨Γ, Δ⟩ is in the frame iff Γ |~ Δ.
  (Frame-to-base uses Containment for the pairs that are in the frame by overlap.)

## L5′. Skolem pair (Lemma 5 with both round trips)

`SkolemPair N V G H νsk σ`, existence `exists_skolemPair`.

Statement. If N is admissible for G, H, V (Definition 12) there are ν_sk and σ with:

1. `mem`: ν_sk sends the blank nodes of G into N;
2. `fixes`: σ fixes L ∪ V;
3. `back`: σ(ν_sk(G)) = G;
4. `fixH`: σ(x) = x for every term x of H;
5. `undo`: σ(ν_sk(x)) = x for every term x of G;
6. `redo`: ν_sk(σ(x)) = x for every term x of ν_sk(G).

Hypothesis used: only the `skolem` field of admissibility: an sk injective on the blank
nodes of G whose values are in N and are not names of G, not names of H, not in V.

Steps.
* Take ν_sk(b) = sk(b) and σ = `skolemInv`: σ sends sk(b) to b for b a blank node of G and
  fixes every other term.
* (5) by cases on x: a blank node b of G goes to sk(b) and back (injectivity of sk); an IRI
  of G is not a Skolem IRI (Skolem IRIs are not names of G); a literal is fixed.
* (1) is the membership half of the hypothesis. (2): literals are fixed; an IRI of V is
  not a Skolem IRI. (3) from (5). (4): an IRI of H is not a Skolem IRI (not a name of H);
  blank nodes and literals are fixed. (6) from (5), since every term of ν_sk(G) is ν_sk(y)
  for a term y of G.

Consequences used later:
* σ is a renaming of ν_sk(G), with inverse the substitution ν_sk (which fixes L ∪ V because
  a substitution moves only blank nodes), by (2) and (6).
* The substitution ν_sk is a renaming of G, with inverse σ, by (2) and (5).

## L4′. Witness coordinate, generalised

`witness_coordinate'`. If terms(X) ⊆ terms(G) ∪ V, μ₀(H) ⊆ X and ν₀ ∈ IMap(N, G), then
ν₀ ∘ μ₀ ∈ IMap(N, H).

Hypotheses used: admissibility for "names of G are in N" and "V ⊆ N".

Steps. Let b be a blank node of H. Then μ₀(b) is a term of X, so a term of G or an IRI of
V. If it is a blank node of G, ν₀ sends it into N. If it is a name of G, it is in N and the
substitution fixes it. If it is in V, it is in N and fixed.

Difference from Lemma 4: X was cl_R(G); now it is any graph over the terms of G and V. It
is applied with X = Cons(G), using (C2).

## Ground graphs

`IMap_of_ground`: every map is an instance mapping for a ground graph.
`Graph.inst_of_ground` (existing): ν(X) = X for ground X.

Used as: Γ = ν_sk(G) is over N (`Graph.inst_subset_lex`, from `mem` and names of G in N),
hence ground because N contains only names (`Admissible.names`). So ν(Γ) = Γ for every ν,
every ν is an instance mapping of Γ, and for nonempty x the antecedent ⋃_{ν ∈ x} ν(Γ) is Γ.

## TG-H. The general theorem in the Herbrand model (counterpart of Lemma 7)

`ConsBase.witness_characterization`.

Statement. N admissible for G, H, V; N nonempty; (ν_sk, σ) a Skolem pair. Then
⟦ν_sk(G)⟧ |~ ⟦H⟧ in the Herbrand model of the base iff Cons(G) simply entails H.

Write Γ = ν_sk(G).

Only if. Suppose the left side and, for contradiction, that no μ has μ(H) ⊆ Cons(G).

1. Claim: for every μ ∈ IMap(N, H), μ(H) \ Cons(Γ) is nonempty. Otherwise
   μ(H) ⊆ Cons(Γ). Apply σ:
   (σ ∘ μ)(H) = σ(μ(H)) (by `fixH`) ⊆ σ(Cons(Γ)) ⊆ Cons(σ(Γ)) (by (C3), σ a renaming of Γ)
   = Cons(G) (by `back`). So σ ∘ μ witnesses simple entailment, contradiction.
2. Instantiate the unfolded implication at x = {ν_sk} and the selection
   S(μ) = μ(H) \ Cons(Γ), which is legitimate by step 1. The antecedent is Γ. So
   ⟨Γ, ⋃_μ S(μ)⟩ is in the frame, and both sides are over N, so Γ |~ ⋃_μ S(μ).
3. First disjunct: some t ∈ S(μ) ∩ Cons(Γ). Impossible by the definition of S.
4. Second disjunct: ⋃_μ S(μ) = ∅. **This is where N nonempty is used**: a constant map
   into N is in IMap(N, H), and its S is nonempty by step 1. Contradiction.

If. Let μ₀(H) ⊆ Cons(G). Fix a nonempty x and a selection S; the antecedent is Γ. It
suffices to find a triple in ⋃_μ S(μ) ∩ Cons(Γ).

1. μ′ = ν_sk ∘ μ₀ is in IMap(N, H), by L4′ with X = Cons(G) and (C2).
2. Pick b ∈ S(μ′) (nonempty). Then b ∈ μ′(H) = ν_sk(μ₀(H)) (`Graph.inst_inst`)
   ⊆ ν_sk(Cons(G)) ⊆ Cons(ν_sk(G)) = Cons(Γ), by (C3) with the substitution ν_sk as a
   renaming of G.

For the prose:
* Compared with Lemma 7, the antecedent side has collapsed to a single instance. That is
  the whole simplification Skolemization buys.
* (C3) is used twice, once with σ and once with ν_sk: the two round trips.
* Step 4 of "only if" has no counterpart under explosion; Theorem 2 does not need N
  nonempty.

## TG-P. Incoherence (counterpart of Proposition 2)

`ConsBase.incoherent_iff_inc`. N admissible, (ν_sk, σ) a Skolem pair. Then ⟦ν_sk(G)⟧ |~ ∅
in the Herbrand model iff Inc(G). N nonempty is **not** needed.

* Only if: instantiate at x = {ν_sk}: ⟨Γ, ∅⟩ is in the frame, so Γ |~ ∅. The first disjunct
  is impossible (∅ meets nothing), so Inc(Γ); then Inc(σ(Γ)) = Inc(G) by (C4) and `back`.
* If: Inc(G) gives Inc(ν_sk(G)) by (C4) with ν_sk; so Γ |~ ∅ and the pair is in the frame.

For the prose: stated in the Herbrand model, as Proposition 2 is. There is no fit-models
version in the Lean.

## TG. The general theorem, part (T)

`ConsBase.general`. Same hypotheses as TG-H. Then
ν_sk(G) ⊨_B H iff Cons(G) simply entails H.

Steps. Theorem 1 (`recovery`) applied to the ground graph ν_sk(G) and to H (it needs only
that their names are in N), then TG-H.

For the prose: Theorem 1 is used unchanged. It never assumed anything about the base
beyond Containment.

## TG-I. Independence, part (I)

`ConsBase.general_independent`, `ConsBase.incoherent_independent`. For two admissible
nonempty N, N′ and two Skolem pairs, the two verdicts agree. Immediate: the right-hand
sides of TG and TG-P mention neither N nor the Skolemization. (The incoherence version
does not need nonemptiness.)

## The regime base without explosion, and agreement with Theorem 2

`Regime.consBase`: Cons = cl, Inc = R-inconsistent. (C1) `subset_clPos`; (C2)
`terms_clPos_subset`; (C3) `clPos_map` (Lemma 6, which holds for every map fixing L ∪ V,
so in particular for renamings); (C4) `inconsistent_map`.

`Regime.fitEnt_skolem_iff`: if G is R-consistent then G ⊨_{B_R} H (Definition 11 on both
sides, explosive base) iff ν_sk(G) ⊨ H in the non-exploding base. Steps: Theorem 2 on the
left gives "R-inconsistent or cl(G) simply entails H"; TG on the right gives "cl(G) simply
entails H"; consistency removes the first disjunct.

For the prose: this is the precise sense in which Theorem 2 is the special case, and it is
restricted to R-consistent G. On inconsistent G the two bases differ by design (explosion).

---

# Part 2. Lemma A and the properties (`ISRDF/Entries.lean`)

## L6=. Renamings commute with closure

`Regime.mapT_clPos`: if ρ is a renaming of X then ρ(cl(X)) = cl(ρ(X)).
`Regime.renames_clPos`: a renaming of X is a renaming of cl(X) (terms of cl(X) are terms
of X or in V; both maps fix V). General form: `Renames.of_terms_subset`.

Steps for the equality. ⊆ is Lemma 6. For ⊇: take t ∈ cl(ρ(X)). Then ρ′(t) ∈ cl(ρ′(ρ(X)))
= cl(X) by Lemma 6 for ρ′ and the round trip. And ρ(ρ′(t)) = t because every term of t is
ρ(y) for a term y of X, or is in V.

For the prose: Lemma 6 gives an inclusion for all maps; equality needs a renaming. This is
the one new closure fact.

## D4. One round of defaults, abstractly

`DefaultStep`: a function D* on graphs and a predicate Incompat on graphs with

* (S1) terms(D*(K)) ⊆ terms(K) ∪ V;
* (S2) if ρ is a renaming of K then ρ(D*(K)) ⊆ D*(ρ(K));
* (S3) if ρ is a renaming of K and Incompat(K) then Incompat(ρ(K)).

## Layer 1. A regime with a default step is a ConsBase

`Regime.consBaseOf R D`:
Cons(X) = cl(cl(X) ∪ D*(cl(X))); Inc(X) iff X is R-inconsistent or Incompat(cl(X)).

* (C1): X ⊆ cl(X) ⊆ cl(cl(X) ∪ …).
* (C2): range restriction of R twice, and (S1).
* (C3): ρ(cl(cl X ∪ D*(cl X))) ⊆ cl(ρ(cl X) ∪ ρ(D*(cl X))) (Lemma 6)
  = cl(cl(ρX) ∪ ρ(D*(cl X))) (L6=) ⊆ cl(cl(ρX) ∪ D*(cl(ρX))) ((S2) at K = cl X, using
  that ρ renames cl X, and L6= again; monotonicity of cl).
* (C4): R-inconsistency by `inconsistent_map`; Incompat by (S3) and L6=.

With no defaults (`DefaultStep.empty`): Cons = cl (`consBaseOf_empty_cons`, by idempotence
of cl) and Inc = R-inconsistency (`consBaseOf_empty_inc`).

## P2. Materialization

`Regime.consBaseOf_cons_union`, `Regime.consBaseOf_inc_union`. For any default step: if
T ⊆ cl(X) then Cons(X ∪ T) = Cons(X), and Inc(X ∪ T) iff Inc(X).

Steps. cl(X ∪ T) = cl(X) (`clPos_union_of_subset`: monotonicity and idempotence), and
R-inconsistency of X ∪ T iff of X (`inconsistent_union_iff`). Cons and Inc depend on X only
through cl(X) and R-inconsistency.

For the prose:
* Proved at layer 1, so it holds for any one-round step, not only for entries.
* It is also the precise content of "Cut and Cautious Monotony can fail only at
  consequences outside cl_R(Γ)": for A ∈ cl(Γ), adding A changes nothing.

## D5. Ground entries

`Entry`: premises A (a graph), conclusion c (a triple, or none for ⊥), defeaters E (a set
of graphs). `Entry.Applies e K`: A ⊆ K and no D ∈ E has D ⊆ K.

`Entries`: a set of ground entries with

* (E1) range: every term of a conclusion is a term of the premises or an IRI of V;
* (E2) uniformity, for renaming pairs only: for ρ, ρ′ fixing L ∪ V with ρ′ ∘ ρ the
  identity on the terms of e's premises, there is an entry e′ in the set with premises
  ρ(A), conclusion ρ(c), and ρ′(D′) a defeater of e for every defeater D′ of e′.

D*(K) = conclusions of the entries applying at K (`Entries.dstar`).
Incompat(K) = some entry with conclusion ⊥ applies at K (`Entries.Incompat`).

For the prose:
* (E2) is not closure under all maps fixing L ∪ V. Defeat is not preserved by maps that
  merge terms. This is the difference from regime uniformity.
* A defeater pattern with variables of its own is the family of all its ground instances.
* Guards are absorbed into which ground entries are in the set.

## Application is invariant

`Entries.applies_map`. If ρ is a renaming of K and e applies at K, then some e′ in the set
applies at ρ(K) and has conclusion ρ(c).

Steps. (E2) with ρ and its inverse ρ′ (the premises are in K, so ρ′ρ is the identity on
their terms) gives e′. Premises: ρ(A) ⊆ ρ(K). Defeaters: if D′ ⊆ ρ(K) for a defeater D′ of
e′, then ρ′(D′) ⊆ ρ′(ρ(K)) = K and ρ′(D′) is a defeater of e, contradicting that e applies.

## Lemma A

`Entries.step` (the entries give a default step) and `Regime.entriesBase R E` (so a regime
with entries is a ConsBase).

* (S1) from (E1) and "premises ⊆ K". (S2), (S3) from `applies_map`.

`Regime.entries_general`: TG at this base, with right-hand side
cl(cl(G) ∪ D*(cl(G))) simply entails H.
`Regime.entries_incoherent_iff`: TG-P, with right-hand side "G is R-inconsistent or
Incompat(cl(G))".

## P1. Defeat witness

`Regime.defeat_witness`. If X ⊆ Y, t ∈ Cons(X) and t ∉ Cons(Y), then there is an entry
with a conclusion that applies at cl(X) and has a defeater D with D ⊆ cl(Y) and D ⊄ cl(X).

Steps (contrapositive). Suppose no such entry. cl(X) ⊆ cl(Y). Every entry with a
conclusion applying at cl(X) also applies at cl(Y): its premises are in cl(Y), and a
defeater inside cl(Y) would be the excluded witness (it is not inside cl(X), since the
entry applies there). So D*(cl X) ⊆ D*(cl Y), and Cons(X) ⊆ Cons(Y) by monotonicity of cl.

## P1′. Lost incoherence

`Regime.incoherence_witness`. If X ⊆ Y, Inc(X) and not Inc(Y), then some entry with
conclusion ⊥ applies at cl(X) and has a defeater D with D ⊆ cl(Y) and D ⊄ cl(X).

Note for the prose: R-inconsistency is monotone, so the incoherence of X cannot have come
from the regime; it came from an entry, and the same argument as P1 applies. (I have read
the statement in the check log, not the proof.)

---

# Part 3. Inventory only (`Patterns.lean`, `Examples.lean`)

Taken from the Lean session's report (RESULT.md, addenda 1 and 2). Statements are
machine-checked; I have not ledgered the proofs.

| Item | Lean | Content |
|---|---|---|
| Pattern entries are entries | `patternEntries` | Ground instances of well-formed pattern entries satisfy (E1), (E2) |
| Well-formedness | `PEntry.WF` | IRI constants of premises and defeaters in V; each conclusion term occurs in the premises or is an IRI of V; the guard's projection onto premise variables is invariant under renamings |
| How an entry fires | `PEntry.applies_inst_iff` | Premises in K, and no defeater has an instance in K under a substitution extending the premise bindings |
| Pattern rules are a regime | `patternRegime`, `PRule.WF` | Positive patterns, no guard, no defeaters |
| Admissible guards | `litGuard`, `guardInvariant_litView`, … | Literal comparisons (false unless both literals); X ≠ Y on premise variables; X ≠ k; ∧, ∨ |
| Inadmissible guard | `not_guardInvariant_isBnode` | A test for a blank node is not invariant |
| Case-study shapes | `Shapes.typeEntry`, `excEntry`, `contempEntry`, `caseRegime`, `caseBase` | Type incompatibility with defeaters; exception read from the graph; contemporary with literal guard; the two type rules; the assembled base |
| Shape facts | `type_incoherence_lost`, `exc_defeat`, `contemp_inc_iff` | Incoherence lost by adding a type; a default defeated by exception triples; incoherent iff the guard holds |
| Nonmonotone instance | `Examples.E0_nonmonotone` | a q a ∈ Cons{a p c}, ∉ Cons{a p c, a p a} |
| Def. 11 against Skolem | `Examples.E0_def11_vs_skolem` | G = {a p _:b}, H = {a q a}: holds for ν_sk(G), fails for G under Definition 11 |
| Hypotheses inhabited | `E0_admissible`, `E0_def11_vs_skolem_exists`, `E0_instance_nat` | An admissible N and a Skolemization exist; one instantiation over ℕ |
| Cautious Monotony fails | `Examples.cautious_monotony_fails` | One schema with a defeater |
| Cut fails | `Examples.cut_fails` | Two schemas, no defeater |
| Redundant blank node not inert | `Examples.redundant_bnode_not_inert` | Stated on Cons and simple entailment |

---

# What the English must carry, and what it must not say

Carry:
* "Renaming of a graph", with the definition (D1), wherever invariance is invoked.
* N nonempty for part (T); not for part (P).
* Part (P) is a statement about the Herbrand model.
* The agreement with Theorem 2 is for R-consistent graphs.
* The well-formedness conditions are sufficient. Necessity is not proved.
* Literal guards are read as false unless both sides are literals.

Do not say:
* "Invariant under permutations" or "under injective maps". Neither is what is proved.
* That Cut fails because of defeat. The Cut witness has no defeater; the cause is one
  round of defaults. Cautious Monotony is the one that needs a defeater.
* That entries are "closed under renamings the way regimes are". Regimes are closed under
  more maps than entries can be.
* That the pipeline's SPARQL is proved correct. `applies_inst_iff` says when one entry
  fires; agreement of the pipeline with Cons is checked by an independent implementation.

Not in the Lean at all (so paper-only if claimed): Corollaries 2 and 3; necessity of the
well-formedness conditions; a fit-models version of part (P); the draft Wikidata entries
themselves (only their shapes).
