# Proof ledger: one spine for the monotone and the general case (`ISRDF/Bridge.lean`)

Prepared Sat 14 Nov 2026 by the Claude Code session, from the uncommitted working tree of
`iss-rdf-lean` at HEAD `e7380ff` (seven modules, `lake build` green, no `sorry`; check log
`handoff/lean-check-2026-11-14-bridge-import.log`).

Purpose: raw material for the English proofs, which Brad writes. Each item gives the
statement in the paper's notation, the Lean name and line in `Bridge.lean`, every
hypothesis with the step that uses it, and the proof steps in order. Nothing here is paper
prose.

Coverage: every declaration of `Bridge.lean`, ledgered from a full reading of the Lean.
This file continues `proof-ledger.md` and uses its item names (D1 to D3, (C1) to (C4),
L4′, L5′, TG-H, TG-P, TG). It does not change that file. Definition and lemma numbers are
the ones in the Lean docstrings (Definition 10 for ground contents, Definition 11 for
graphs with blank nodes, Lemma 7, Proposition 2, Theorems 1 and 2).

## Notation added to that of `proof-ledger.md`

| Here | Meaning | Lean |
|---|---|---|
| Γ ground | every term of Γ is a name (an IRI or a literal) | `Graph.Ground` |
| B(Γ) | the bearers of Γ in a model M | `M.brG Γ` |
| B^e | the base of Cons and Inc with explosion flag e | `C.baseWith e N` |
| ⟦G⟧ incoherent in M | ⟦G⟧ implies the empty succedent in M | `M.Incoherent N G` |

"Unfolded implication" in a model M (`Model.gEnt_iff`, which is Lemma 3): ⟦G⟧ |~ ⟦H⟧ iff for
every nonempty x ⊆ IMap(N, G) and every selection S (a nonempty S(μ) ⊆ B(μ(H)) for each
μ ∈ IMap(N, H)), the pair ⟨⋃_{ν ∈ x} B(ν(G)), ⋃_μ S(μ)⟩ is a good implication of M.

"Unfolded incoherence" (`Model.incoherent_iff`): ⟦G⟧ is incoherent in M iff for every
nonempty x ⊆ IMap(N, G) the pair ⟨⋃_{ν ∈ x} B(ν(G)), ∅⟩ is a good implication of M.

In the Herbrand model B(Γ) = Γ (`Base.herbrand_brG`) and "good implication" is membership
in the frame.

## The chain, in one view

For a base B^e whose Cons and Inc are monotone and invariant under instance mappings
(B13), and N admissible with (e or N nonempty):

| Step | Statement | Item |
|---|---|---|
| 1 | G ⊨ H in the fit models iff ⟦G⟧ \|~ ⟦H⟧ in the Herbrand model | Theorem 1 (`recovery`) |
| 2 | iff ⟦ν_sk(G)⟧ \|~ ⟦H⟧ in the Herbrand model | B16, the bridge |
| 3 | iff (e and Inc(G)) or Cons(G) simply entails H | B9 |

Steps 1 and 3 hold for every `ConsBase`. Step 2 from left to right holds for every base
and every model (B5). Step 2 from right to left is the only place monotonicity is used
(B14).

The Lean composes these through the fit models: B18 is Theorem 1 at (G, H), B16, and
Theorem 1 at (ν_sk(G), H) read backwards; B11 is Theorem 1 at (ν_sk(G), H) and B9; B19 is
B18 then B11. So Theorem 1 is invoked three times and two of the invocations cancel.

---

# Part 4. Ground antecedents

## B1. An instance over an admissible N is ground

`Admissible.inst_ground` (line 42). If N is admissible for G, H, V and ν ∈ IMap(N, G), then
ν(G) is ground.

Hypotheses used: names of G are in N (`hG`); N contains only names (`names`).

Steps. ν(G) ⊆ Lex(N), because the names of G are in N and ν sends the blank nodes of G into
N (`Graph.inst_subset_lex`). So every term of ν(G) is in N (`Graph.subset_lex_iff`), and N
contains only names (`Graph.ground_of_over`).

## B2. The instances of a ground graph have the bearers of the graph

`Model.biUnion_inst_of_ground` (line 52). Any model M. If Γ is ground and x is a nonempty
set of maps, then ⋃_{ν ∈ x} B(ν(Γ)) = B(Γ).

Steps. ⊆: ν(Γ) = Γ for every ν (`Graph.inst_of_ground`). ⊇: take ν₀ ∈ x; B(Γ) = B(ν₀(Γ)).

Not assumed: that x ⊆ IMap(N, Γ).

## B3. A ground antecedent is one pair

`Model.gEnt_ground_iff` (line 68). Any model M, any N, any H. If Γ is ground and ν₀ is any
map, then ⟦Γ⟧ |~ ⟦H⟧ in M iff for every selection S the pair ⟨B(Γ), ⋃_μ S(μ)⟩ is a good
implication of M.

Hypotheses used: groundness, in both directions. ν₀ only witnesses that there is a
nonempty family of instance mappings.

Steps. Start from the unfolded implication.
* Left to right: instantiate at x = {ν₀}. This is allowed because every map is an instance
  mapping of a ground graph (`IMap_of_ground`). The antecedent is B(Γ) by B2.
* Right to left: for any nonempty x the antecedent is B(Γ) by B2.

For the prose:
* This is the reduction of Definition 11 to Definition 10 on the antecedent side only. The
  succedent H keeps its selections.
* In `General.lean` the same reduction was done inline inside TG-H (the "Ground graphs"
  paragraph of `proof-ledger.md`). Here it is a lemma about every model.

## B4. A ground antecedent is one pair, for incoherence

`Model.incoherent_ground_iff` (line 85). Any model M. If Γ is ground and ν₀ is any map, then
⟦Γ⟧ is incoherent in M iff ⟨B(Γ), ∅⟩ is a good implication of M.

Steps. As B3, from the unfolded incoherence.

---

# Part 5. Definition 11 gives the Skolem reading

## B5. From G to a ground instance of G, in one model

`Model.gEnt_inst_of_gEnt` (line 103). Any model M. If ν ∈ IMap(N, G), ν(G) is ground and
⟦G⟧ |~ ⟦H⟧ in M, then ⟦ν(G)⟧ |~ ⟦H⟧ in M.

Hypotheses used: ν ∈ IMap(N, G), so that {ν} is one of the families Definition 11 ranges
over; groundness of ν(G), for B3.

Steps.
1. By B3 (with ν₀ = ν) it is enough to show, for every selection S, that
   ⟨B(ν(G)), ⋃_μ S(μ)⟩ is a good implication.
2. Instantiate the unfolded implication for G at x = {ν} and the same S. Its antecedent is
   ⋃_{ν′ ∈ {ν}} B(ν′(G)) = B(ν(G)).

`Model.incoherent_inst_of_incoherent` (line 113) is the same for incoherence, with B4 in
place of B3.

For the prose:
* Nothing is assumed about M: not fitness, not that it is the Herbrand model.
* The selections S on the succedent side are the same on both sides, because H is the same.
* One direction only. The converse is B14 and needs the base to be monotone.

## B6. The same in the fit models

`fitEnt_inst_of_fitEnt` (line 125). For every base B over N: if ν ∈ IMap(N, G), ν(G) is
ground and G ⊨_B H, then ν(G) ⊨_B H.

Steps. B5 in each model fit for B.

For the prose:
* Nothing is assumed about the base beyond its being a base.
* The converse fails for the entries base of Example 1b: `Examples.E0_def11_vs_skolem` has
  ν_sk(G) ⊨ H and not G ⊨ H, for G = {a p _:b} and H = {a q a}.

---

# Part 6. The base with an explosion flag

## B7. Bases with the same relation are equal

`Base.ext_rel` (line 133). If Γ |~ Δ in B iff Γ |~ Δ in B′, for all Γ and Δ, then B = B′.

Lean bookkeeping (a base is a relation together with a proof of Containment). It is what
allows B8 and B22 to be stated as equalities of bases. No counterpart is needed on paper.

## B8. The base B^e

`ConsBase.baseWith e N` (line 147). For a proposition e:
Γ |~ Δ iff Δ ∩ Cons(Γ) ≠ ∅, or Inc(Γ) and (e or Δ = ∅).

* It is a base: Containment from (C1), as for D3.
* `baseWith_false` (line 152): with e false it is the base of D3 (`ConsBase.base`). The two
  relations differ only in the order of two conjuncts.
* With e true the relation is: Δ ∩ Cons(Γ) ≠ ∅, or Inc(Γ).
* `mem_frame_with_iff` (line 165): for Γ, Δ ⊆ Lex(N), ⟨Γ, Δ⟩ is in the frame iff Γ |~ Δ.
  (`Base.rel_of_mem_frame`, `Base.mem_frame_of_rel`, which hold for every base.)

For the prose:
* e is a proposition, not a property of Γ. Only e true and e false are used.
* With e true an incoherent Γ implies every Δ. With e false it implies ∅ and whatever
  meets Cons(Γ), as in D3.

## B9. The general theorem in the Herbrand model, with or without explosion

`ConsBase.witness_characterization_with` (line 177).

Statement. N admissible for G, H, V; e or N nonempty; (ν_sk, σ) a Skolem pair. Then
⟦ν_sk(G)⟧ |~ ⟦H⟧ in the Herbrand model of B^e iff (e and Inc(G)) or Cons(G) simply entails H.

Write Γ = ν_sk(G). Preliminaries, as in TG-H:
* Γ ⊆ Lex(N) (`mem`, names of G in N); Γ is ground (B1).
* σ is a renaming of Γ (`fixes`, `redo`); the substitution ν_sk is a renaming of G
  (`undo`).
* By B3 with ν₀ = ν_sk, the left side is: for every selection S, ⟨Γ, ⋃_μ S(μ)⟩ is in the
  frame.

Only if. Suppose the left side and, for contradiction, that neither (e and Inc(G)) nor any
μ with μ(H) ⊆ Cons(G).

0. Inc(Γ) implies Inc(G): (C4) with σ a renaming of Γ gives Inc(σ(Γ)), and σ(Γ) = G by
   `back`.
1. Claim: for every μ ∈ IMap(N, H), μ(H) \ Cons(Γ) is nonempty. Otherwise μ(H) ⊆ Cons(Γ),
   and (σ ∘ μ)(H) = σ(μ(H)) (by `fixH`) ⊆ σ(Cons(Γ)) ⊆ Cons(σ(Γ)) (by (C3)) = Cons(G) (by
   `back`), so σ ∘ μ witnesses simple entailment. (Step 1 of TG-H, unchanged.)
2. Take the selection S(μ) = μ(H) \ Cons(Γ), legitimate by step 1. ⋃_μ S(μ) ⊆ Lex(N)
   (names of H in N). So Γ |~ ⋃_μ S(μ) in B^e, by `mem_frame_with_iff`. Three cases.
3. Some t ∈ ⋃_μ S(μ) is in Cons(Γ). Impossible by the definition of S.
4. Inc(Γ) and e. Then Inc(G) by step 0, so (e and Inc(G)). Contradiction.
5. Inc(Γ) and ⋃_μ S(μ) = ∅. Split the hypothesis "e or N nonempty".
   * e: as step 4.
   * N has a member n: the constant map to n is in IMap(N, H), and its S is nonempty by
     step 1. Contradiction.

If. Fix a selection S. ⋃_μ S(μ) ⊆ Lex(N). It is enough to show Γ |~ ⋃_μ S(μ) in B^e.

* Case e and Inc(G): Inc(ν_sk(G)) by (C4) with the substitution ν_sk as a renaming of G.
  With e this is the second disjunct of B^e.
* Case μ₀(H) ⊆ Cons(G): μ′ = ν_sk ∘ μ₀ is in IMap(N, H) by L4′ with X = Cons(G) and (C2).
  Pick b ∈ S(μ′). Then b ∈ μ′(H) = ν_sk(μ₀(H)) (`Graph.inst_inst`) ⊆ ν_sk(Cons(G))
  ⊆ Cons(ν_sk(G)) = Cons(Γ), by (C3). (The "if" of TG-H, unchanged.)

Where each hypothesis is used:

| Hypothesis | Used in |
|---|---|
| e or N nonempty | step 5 of "only if" only |
| e, when it holds | steps 4 and 5 of "only if"; first case of "if" |
| (C3) | step 1 (with σ); second case of "if" (with ν_sk) |
| (C4) | step 0 (with σ); first case of "if" (with ν_sk) |
| (C2) | second case of "if", through L4′ |
| (C1) | only through B^e being a base |

For the prose:
* Against TG-H, the new material is step 0, step 4, the first branch of step 5 and the
  first case of "if". Everything else is the TG-H proof.
* With e true, N may be empty. With e false, the statement is TG-H.
* (C4) is used in both directions here; in TG-H it is not used at all (it is used in
  TG-P).

## B10. Incoherence, with or without explosion

`ConsBase.incoherent_iff_inc_with` (line 261). N admissible, (ν_sk, σ) a Skolem pair. Then
⟦ν_sk(G)⟧ is incoherent in the Herbrand model of B^e iff Inc(G).

Not needed: e, N nonempty.

Steps. By B4 with ν₀ = ν_sk, the left side is: ⟨Γ, ∅⟩ is in the frame, that is, Γ |~ ∅ in
B^e: ∅ ∩ Cons(Γ) ≠ ∅, or Inc(Γ) and (e or ∅ = ∅).
* Only if: the first disjunct is impossible. The second gives Inc(Γ), hence Inc(G) by (C4)
  with σ and `back`.
* If: Inc(G) gives Inc(ν_sk(G)) by (C4) with ν_sk. The second disjunct holds with ∅ = ∅.

For the prose: the flag makes no difference because the succedent is empty. Stated in the
Herbrand model, as TG-P and Proposition 2 are.

## B11. The general theorem, with or without explosion

`ConsBase.general_with` (line 283). Same hypotheses as B9. Then
ν_sk(G) ⊨_{B^e} H iff (e and Inc(G)) or Cons(G) simply entails H.

Steps. Theorem 1 (`recovery`) applied to Γ and H (names of Γ in N because Γ ⊆ Lex(N);
names of H in N by admissibility), then B9.

## B12. The results of `General.lean` as the case e false

`ConsBase.witness_characterization_of_with` (line 294), `incoherent_iff_inc_of_with` (line
303), `general_of_with` (line 311). They have the statements of TG-H, TG-P and TG.

Steps. Rewrite the base by `baseWith_false`. Apply B9, B10 or B11 with the hypothesis "N
nonempty" as the second disjunct of "e or N nonempty". Remove the disjunct (false and
Inc(G)).

Checked in Lean: each of the three has a statement definitionally equal to that of the
`General.lean` original (the two proofs are identified by `rfl`; log
`handoff/lean-check-2026-11-14-bridge.log`).

---

# Part 7. The bridge

## B13. Monotone and invariant under instance mappings

`ConsBase.InstMonotone` (line 324). A property of a `ConsBase`:

* (M1) X ⊆ Y implies Cons(X) ⊆ Cons(Y). `cons_mono`
* (M2) X ⊆ Y and Inc(X) imply Inc(Y). `inc_mono`
* (M3) ν(Cons(X)) ⊆ Cons(ν(X)), for every substitution ν of terms for blank nodes and
  every X. `cons_inst`
* (M4) Inc(X) implies Inc(ν(X)), for every such ν and every X. `inc_inst`

For the prose:
* (M3) and (M4) quantify over every substitution for blank nodes, including ones that send
  two blank nodes to one term or a blank node to a term already in X. Such a ν need not be
  a renaming of X.
* (C3) and (C4) quantify over renamings, which need not be substitutions for blank nodes
  (σ is not one: it moves Skolem IRIs). So neither pair of conditions is stated as a
  special case of the other.
* (M3) and (M4) are one-directional, like (C3) and (C4).
* N does not occur. ν ranges over all maps, not over IMap(N, X).

## B14. From the right-hand side to Definition 11 (the "if" half of Lemma 7)

`ConsBase.InstMonotone.gEnt_of_cons` (line 336).

Statement. (M1) to (M4); N admissible for G, H, V. If (e and Inc(G)) or Cons(G) simply
entails H, then ⟦G⟧ |~ ⟦H⟧ in the Herbrand model of B^e, with G read by Definition 11.

Not needed: a Skolem pair; e or N nonempty.

Steps. Start from the unfolded implication. Fix a nonempty x ⊆ IMap(N, G) and a selection
S. Write A = ⋃_{ν ∈ x} ν(G). A ⊆ Lex(N) (names of G in N) and ⋃_μ S(μ) ⊆ Lex(N) (names of H
in N), so it is enough to show A |~ ⋃_μ S(μ) in B^e. Take ν₀ ∈ x; then ν₀(G) ⊆ A.

* Case e and Inc(G): Inc(ν₀(G)) by (M4); Inc(A) by (M2). With e this is the second disjunct.
* Case μ₀(H) ⊆ Cons(G):
  1. μ′ = ν₀ ∘ μ₀ is in IMap(N, H), by L4′ with X = Cons(G), (C2) and ν₀ ∈ IMap(N, G).
  2. Pick b ∈ S(μ′). Then b ∈ μ′(H) = ν₀(μ₀(H)) (`Graph.inst_inst`) ⊆ ν₀(Cons(G))
     ⊆ Cons(ν₀(G)) (by (M3)) ⊆ Cons(A) (by (M1)).

Where each hypothesis is used:

| Hypothesis | Used in |
|---|---|
| x nonempty (part of Definition 11) | choice of ν₀ |
| (M4), (M2) | first case |
| (M3), (M1) | second case, step 2 |
| (C2), names of G in N, V ⊆ N | second case, step 1, through L4′ |
| (C3), (C4) | not used |

For the prose:
* This has the shape of the "if" half of Lemma 7 (`Semantics.lean`, lines 647 to 675), with
  Cons for cl and (M1), (M3) for monotonicity of closure and Lemma 6.
* The witness is pushed through an arbitrary ν₀ ∈ x, not through ν_sk. That is why (M3) is
  needed for every substitution and (C3) for renamings is not enough.
* If IMap(N, G) is empty there is no nonempty x and the conclusion holds vacuously.

## B15. From Inc(G) to incoherence under Definition 11 (the "if" half of Proposition 2)

`ConsBase.InstMonotone.incoherent_of_inc` (line 372). (M2), (M4); names of G in N. If
Inc(G), then ⟦G⟧ is incoherent in the Herbrand model of B^e, with G read by Definition 11.

Steps. From the unfolded incoherence. Fix a nonempty x ⊆ IMap(N, G); A ⊆ Lex(N). Take
ν₀ ∈ x. Inc(ν₀(G)) by (M4); Inc(A) by (M2). The second disjunct of B^e holds with ∅ = ∅.

Hypotheses: only "names of G are in N" from admissibility. (M1) and (M3) are not used.

## B16. The bridge, in the Herbrand model

`ConsBase.InstMonotone.gEnt_iff_skolem` (line 391).

Statement. (M1) to (M4); N admissible; e or N nonempty; (ν_sk, σ) a Skolem pair. Then, in
the Herbrand model of B^e, ⟦G⟧ |~ ⟦H⟧ iff ⟦ν_sk(G)⟧ |~ ⟦H⟧.

Steps.
* Left to right: B5 with ν = ν_sk (`mem`; ν_sk(G) is ground by B1).
* Right to left: B9, left to right, gives (e and Inc(G)) or Cons(G) simply entails H. Then
  B14.

Where each hypothesis is used:

| Hypothesis | Used in |
|---|---|
| (M1) to (M4) | right to left only, through B14 |
| e or N nonempty | right to left only, through B9 |
| the Skolem pair beyond `mem` | right to left only, through B9 |

## B17. The bridge for incoherence

`ConsBase.InstMonotone.incoherent_iff_skolem` (line 401). (M1) to (M4) (only (M2) and (M4)
are used); N admissible; a Skolem pair. Then, in the Herbrand model of B^e, ⟦G⟧ is
incoherent iff ⟦ν_sk(G)⟧ is incoherent.

Steps. Left to right: the incoherence form of B5. Right to left: B10, then B15.

Not needed: e or N nonempty.

## B18. The bridge, in the fit models

`ConsBase.InstMonotone.fitEnt_iff_skolem` (line 410). Hypotheses of B16. Then
G ⊨_{B^e} H iff ν_sk(G) ⊨_{B^e} H.

Steps. Theorem 1 at (G, H); B16; Theorem 1 at (ν_sk(G), H), read from right to left.

## B19. The general theorem with Definition 11 in antecedent position

`ConsBase.InstMonotone.general_def11` (line 423).

Statement. (M1) to (M4); N admissible; e or N nonempty. Then
G ⊨_{B^e} H iff (e and Inc(G)) or Cons(G) simply entails H.

Steps. Take a Skolem pair (L5′, `exists_skolemPair`). B18, then B11.

For the prose:
* No Skolemization appears in the statement. It appears only inside the proof.
* With e false this is a statement about monotone bases without explosion, and it needs N
  nonempty.

## B20. Proposition 2 with Definition 11, on a monotone base

`ConsBase.InstMonotone.incoherent_def11` (line 430). (M1) to (M4); N admissible for G, H,
V, for some H. Then ⟦G⟧ is incoherent in the Herbrand model of B^e iff Inc(G).

Steps. Take a Skolem pair. B17, then B10.

---

# Part 8. Theorem 2 and Proposition 2 as corollaries

## B21. A regime is monotone and invariant under instance mappings

`Regime.consBase_instMonotone` (line 444). For Cons = cl and Inc = R-inconsistent
(`Regime.consBase`):

* (M1) `clPos_mono`. (M2) `inconsistent_mono`.
* (M3) Lemma 6 (`clPos_map`) at the substitution ν, which fixes L ∪ V because it moves only
  blank nodes (`fixesLV_subst`).
* (M4) `inconsistent_map` at the same map.

For the prose: Lemma 6 holds for every map fixing L ∪ V, so in particular for substitutions
that merge terms. Entries are required to be invariant under renamings only (D1, D5).

## B22. B_R is the exploding base of cl and R-inconsistency

`Regime.base_eq_baseWith` (line 451). B_R = B^e for Cons = cl, Inc = R-inconsistent and e
true.

Steps. B_R is: R-inconsistent(Γ), or Δ ∩ cl(Γ) ≠ ∅. B^e with e true is: Δ ∩ cl(Γ) ≠ ∅, or
R-inconsistent(Γ) and (true or Δ = ∅). The same relation; B7.

## B23. The bridge over B_R

`Regime.fitEnt_iff_skolem` (line 465). N admissible, (ν_sk, σ) a Skolem pair. Then
G ⊨_{B_R} H iff ν_sk(G) ⊨_{B_R} H.

Steps. B22; B21; B18 with e true (so "e or N nonempty" holds by e).

Not needed: G R-consistent; N nonempty.

For the prose: this is a different statement from `Regime.fitEnt_skolem_iff` (the last item
of Part 1 in `proof-ledger.md`). That one compares B_R with the non-exploding base of cl
and needs G R-consistent and N nonempty. This one has B_R on both sides and holds for every
admissible G, R-inconsistent ones included.

## B24. Theorem 2 from the general theorem

`closure_regimes_of_general` (line 478). N admissible for G, H, V. Then
G ⊨_{B_R} H iff G R-entails H.

Steps. B22. B19 for the regime (B21) with e true. The result is (true and R-inconsistent(G))
or cl(G) simply entails H, which is the definition of R-entailment (`Regime.Entails`).

Checked in Lean:
* The statement is definitionally equal to that of `closure_regimes` (`rfl`).
* A walk of the dependencies shows this proof does not use `witness_characterization`
  (Lemma 7), `witness_coordinate` (Lemma 4) or `skolemization` (Lemma 5) of
  `Semantics.lean`. It uses `recovery` (Theorem 1), `exists_skolemPair` (L5′),
  `witness_coordinate'` (L4′), `clPos_map` (Lemma 6) and the shapes of Lemma 3. The original
  `closure_regimes` uses all three of the lemmas named first.

## B25. Proposition 2 from the general theorem

`incoherence_recovery_of_general` (line 488). N admissible for G, ∅, V. Then ⟦G⟧ is
incoherent in the Herbrand model of B_R iff G is R-inconsistent.

Steps. B22. B20 for the regime with e true and H = ∅.

Checked in Lean: the statement is definitionally equal to that of `incoherence_recovery`
(`rfl`), and the proof does not use it.

## B26. Lemmas 4 and 5 as special cases

* `witness_coordinate_of_general` (line 496): Lemma 4 is L4′ at X = cl(G), with
  `terms_clPos_subset` for the hypothesis on the terms of X.
* `skolemization_of_skolemPair` (line 503): Lemma 5 is four of the six fields of L5′
  (`mem`, `fixes`, `back`, `fixH`). `undo` and `redo` are the two it lacks.

Checked in Lean: both statements are definitionally equal to the originals (`rfl`).

---

# What the English must carry, and what it must not say

Carry:
* The hypothesis on N is "e or N nonempty". With explosion nothing is asked of N beyond
  admissibility; without it N must be nonempty.
* (M3) and (M4) are for every substitution of terms for blank nodes, merging ones
  included. That is not invariance under renamings.
* From Definition 11 to the Skolem reading: every base, every model (B5, B6). From the
  Skolem reading to Definition 11: bases with (M1) to (M4) (B14).
* Over B_R the two readings agree on every admissible G (B23).
* Incoherence results (B10, B15, B17, B20, B25) are statements about the Herbrand model.
* B19 with e false needs N nonempty.

Do not say:
* That the two readings agree if and only if the base is monotone. Sufficiency is proved.
  For the converse there is one counterexample base (`Examples.E0_def11_vs_skolem`), not a
  theorem.
* That the general theorem with Definition 11 in antecedent position holds for entries
  bases. B19 assumes (M1) to (M4).
* That B14 uses Skolemization, or that B5 uses anything about the base.
* That the proofs in `Semantics.lean` were replaced. Both sets of proofs are in the
  repository; the statements coincide.
* That (M1) to (M4) follow from (C1) to (C4), or the reverse.

Superseded in scope, in `proof-ledger.md`: the note under "The regime base without
explosion, and agreement with Theorem 2" and the "Carry" line "The agreement with Theorem
2 is for R-consistent graphs" are about `Regime.fitEnt_skolem_iff`, which compares two
different bases. They remain true of that statement. B23 and B24 are a second sense in
which Theorem 2 is the special case, and they carry no consistency restriction.

Not in the Lean at all (so paper-only if claimed): necessity of (M1) to (M4) for the
bridge; a fit-models version of the incoherence results; which entries bases, if any,
satisfy (M1) to (M4); Corollaries 2 and 3.
