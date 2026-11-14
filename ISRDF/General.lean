import ISRDF.Semantics

/-!
# Implication-Space Semantics for RDF — Part 3: the general theorem

Theorem 2 of the note is stated for the base `B_R` of a regime, which is monotone and
explosive.  This file states and proves its counterpart for a base given only by a
consequence function `cons` and an incoherence predicate `inc`:

* a graph in antecedent position is read through its Skolemization `ν_sk(G)` (Lemma 5),
  which is ground, so Definition 11 and Theorem 1 (`recovery`) apply to it unchanged;
* a graph in succedent position keeps Definition 11;
* the base is `Γ |~ Δ` iff `Δ` meets `cons Γ`, or `Δ = ∅` and `inc Γ` (no explosion).

`ConsBase.general`:      `ν_sk(G) ⊨ H` in the fit models  iff  `cons G` simply entails `H`.
`ConsBase.incoherent_iff_inc`:  `⟦ν_sk(G)⟧ |∼ ∅`          iff  `inc G`.
`ConsBase.general_independent`, `ConsBase.incoherent_independent`: neither verdict depends
on the Skolemization or on `N`.

Nothing here assumes `cons` monotone.  What is assumed (`ConsBase`): Containment, no new
terms, and invariance under *renamings* of a graph, i.e. maps fixing `L ∪ V` that are undone
on the graph's terms by another map fixing `L ∪ V`.  (The map `σ` of Lemma 5 is not injective
as a total map, since it sends both `sk b` and `b` to `b`; it is a renaming of `ν_sk(G)`.)

The regime base without explosion is an instance (`Regime.consBase`), and
`Regime.fitEnt_skolem_iff` checks the construction against Theorem 2 on consistent graphs.

New relative to the note: `general` needs `N` nonempty.  Without explosion, an empty `N`
and a succedent with blank nodes leave the succedent family empty, and the two sides come
apart when the antecedent is incoherent.
-/

set_option autoImplicit false

namespace ISRDF

variable {Iri Lit Bn : Type}

/-- `ρ` is a renaming of `X` over `V`: it fixes `L ∪ V` and is undone on the terms of `X`
by a map that also fixes `L ∪ V`. -/
structure Renames (V : Set Iri) (ρ : Term Iri Lit Bn → Term Iri Lit Bn)
    (X : Graph Iri Lit Bn) : Prop where
  fixes : FixesLV V ρ
  inv : ∃ ρ' : Term Iri Lit Bn → Term Iri Lit Bn,
    FixesLV V ρ' ∧ ∀ t ∈ X, ∀ x ∈ t.terms, ρ' (ρ x) = x

/-- A base presented by a consequence function and an incoherence predicate. -/
structure ConsBase (Iri Lit Bn : Type) (V : Set Iri) where
  /-- `Cons(X)`: the consequences of `X`, its terms read as constants. -/
  cons : Graph Iri Lit Bn → Graph Iri Lit Bn
  /-- `X` is incoherent. -/
  inc : Graph Iri Lit Bn → Prop
  /-- Containment. -/
  extensive : ∀ X : Graph Iri Lit Bn, X ⊆ cons X
  /-- No new terms (range restriction). -/
  terms_cons : ∀ X : Graph Iri Lit Bn,
    (cons X).terms ⊆ X.terms ∪ ((fun v => Term.iri v) '' V)
  /-- Invariance of consequence under renamings. -/
  cons_map : ∀ (ρ : Term Iri Lit Bn → Term Iri Lit Bn) (X : Graph Iri Lit Bn),
    Renames V ρ X → Graph.mapT ρ (cons X) ⊆ cons (Graph.mapT ρ X)
  /-- Invariance of incoherence under renamings. -/
  inc_map : ∀ (ρ : Term Iri Lit Bn → Term Iri Lit Bn) (X : Graph Iri Lit Bn),
    Renames V ρ X → inc X → inc (Graph.mapT ρ X)

/-- The data of Lemma 5, with the two round trips made explicit. -/
structure SkolemPair (N : Set (Term Iri Lit Bn)) (V : Set Iri) (G H : Graph Iri Lit Bn)
    (νsk : Bn → Term Iri Lit Bn) (σ : Term Iri Lit Bn → Term Iri Lit Bn) : Prop where
  mem : νsk ∈ IMap N G
  fixes : FixesLV V σ
  back : Graph.mapT σ (G.inst νsk) = G
  fixH : ∀ t ∈ H, ∀ x ∈ t.terms, σ x = x
  undo : ∀ t ∈ G, ∀ x ∈ t.terms, σ (Term.subst νsk x) = x
  redo : ∀ t ∈ G.inst νsk, ∀ x ∈ t.terms, Term.subst νsk (σ x) = x

variable {V : Set Iri} {N : Set (Term Iri Lit Bn)}

/-- Lemma 5 again, producing a `SkolemPair`. -/
theorem exists_skolemPair {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) :
    ∃ (νsk : Bn → Term Iri Lit Bn) (σ : Term Iri Lit Bn → Term Iri Lit Bn),
      SkolemPair N V G H νsk σ := by
  obtain ⟨sk, hinj, hsk⟩ := hA.skolem
  have h5 : ∀ t ∈ G, ∀ x ∈ t.terms,
      skolemInv sk G.bnodes
        (Term.subst (fun b => (Term.iri (sk b) : Term Iri Lit Bn)) x) = x := by
    intro t ht x hx
    cases x with
    | bnode b =>
      simp only [Term.subst_bnode]
      exact skolemInv_iri hinj ⟨t, ht, hx⟩
    | iri a =>
      simp only [Term.subst_iri]
      apply skolemInv_of_not
      rintro ⟨b, hb, h⟩
      exact (hsk b hb).2 (Or.inl (Or.inl ⟨trivial, t, ht, h ▸ hx⟩))
    | lit a =>
      simp only [Term.subst_lit]
      exact skolemInv_lit _ _ _
  refine ⟨fun b => Term.iri (sk b), skolemInv sk G.bnodes,
    ⟨fun b hb => (hsk b hb).1, ?_, ?_, ?_, h5, ?_⟩⟩
  · refine ⟨fun l => skolemInv_lit _ _ _, fun v hv => skolemInv_of_not ?_⟩
    rintro ⟨b, hb, h⟩
    exact (hsk b hb).2 (Or.inr ⟨v, hv, h⟩)
  · rw [Graph.inst, Graph.mapT_mapT]
    exact Graph.mapT_eq_self G (fun t ht x hx => h5 t ht x hx)
  · intro t ht x hx
    cases x with
    | bnode b => exact skolemInv_bnode _ _ _
    | lit a => exact skolemInv_lit _ _ _
    | iri a =>
      apply skolemInv_of_not
      rintro ⟨b, hb, h⟩
      exact (hsk b hb).2 (Or.inl (Or.inr ⟨trivial, t, ht, h ▸ hx⟩))
  · rintro _ ⟨t, ht, rfl⟩ x hx
    obtain ⟨y, hy, rfl⟩ := (Triple.mem_terms_map _ _).1 hx
    rw [h5 t ht y hy]

/-- Every mapping is an instance mapping for a ground graph. -/
theorem IMap_of_ground {X : Graph Iri Lit Bn} (hX : X.Ground) (ν : Bn → Term Iri Lit Bn) :
    ν ∈ IMap N X := by
  intro b hb
  obtain ⟨t, ht, hbt⟩ := hb
  exact absurd (hX t ht _ hbt) (by simp [Term.IsName])

theorem Graph.names_subset_of_subset_lex {X : Graph Iri Lit Bn} (h : X ⊆ Lex N) :
    X.names ⊆ N := by
  rintro x ⟨-, t, ht, hx⟩
  exact h ht x hx

/-- Lemma 4 (Witness coordinate) for any `X` whose terms come from `G` and `V`. -/
theorem witness_coordinate' {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    {X : Graph Iri Lit Bn} (hX : X.terms ⊆ G.terms ∪ ((fun v => Term.iri v) '' V))
    {μ₀ : Bn → Term Iri Lit Bn} (hμ₀ : H.inst μ₀ ⊆ X) {ν₀ : Bn → Term Iri Lit Bn}
    (hν₀ : ν₀ ∈ IMap N G) :
    (fun b => Term.subst ν₀ (μ₀ b)) ∈ IMap N H := by
  intro b hb
  obtain ⟨t, ht, hbt⟩ := hb
  have hmem : μ₀ b ∈ X.terms :=
    ⟨_, hμ₀ ⟨t, ht, rfl⟩, (Triple.mem_terms_map _ _).2 ⟨_, hbt, rfl⟩⟩
  rcases hX hmem with ⟨t', ht', hx⟩ | ⟨v, hv, hveq⟩
  · cases hμ : μ₀ b with
    | bnode b' =>
      rw [hμ] at hx
      simp only [hμ, Term.subst_bnode]
      exact hν₀ b' ⟨t', ht', hx⟩
    | iri a =>
      rw [hμ] at hx
      simp only [hμ, Term.subst_iri]
      exact hA.hG ⟨trivial, t', ht', hx⟩
    | lit a =>
      rw [hμ] at hx
      simp only [hμ, Term.subst_lit]
      exact hA.hG ⟨trivial, t', ht', hx⟩
  · show Term.subst ν₀ (μ₀ b) ∈ N
    rw [← hveq]
    simp only [Term.subst_iri]
    exact hA.hV v hv

namespace ConsBase
variable (C : ConsBase Iri Lit Bn V)

/-- The base of a `ConsBase`: `Δ` meets `Cons(Γ)`, or `Δ` is empty and `Γ` is incoherent. -/
def base (N : Set (Term Iri Lit Bn)) : Base N where
  rel Γ Δ := (Δ ∩ C.cons Γ).Nonempty ∨ (Δ = ∅ ∧ C.inc Γ)
  containment := fun Γ _ _ _ ⟨t, ht, ht'⟩ => Or.inl ⟨t, ht', C.extensive Γ ht⟩

theorem mem_frame_iff {Γ Δ : Graph Iri Lit Bn} (hΓ : Γ ⊆ Lex N) (hΔ : Δ ⊆ Lex N) :
    (Γ, Δ) ∈ (C.base N).frame ↔ (Δ ∩ C.cons Γ).Nonempty ∨ (Δ = ∅ ∧ C.inc Γ) :=
  ⟨(C.base N).rel_of_mem_frame hΓ hΔ, (C.base N).mem_frame_of_rel hΓ hΔ⟩

/-- The general theorem in the Herbrand model: the counterpart of Lemma 7. -/
theorem witness_characterization {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    (hN : N.Nonempty) {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    (C.base N).herbrand.GEnt N (G.inst νsk) H ↔ SimpleEntails (C.cons G) H := by
  have hΓlex : G.inst νsk ⊆ Lex N := Graph.inst_subset_lex hA.hG hS.mem
  have hΓground : (G.inst νsk).Ground :=
    Graph.ground_of_over (G.inst νsk) hA.names ((Graph.subset_lex_iff _).1 hΓlex)
  have hinst : ∀ ν : Bn → Term Iri Lit Bn, (G.inst νsk).inst ν = G.inst νsk :=
    fun ν => Graph.inst_of_ground (G.inst νsk) ν hΓground
  have hνall : νsk ∈ IMap N (G.inst νsk) := IMap_of_ground hΓground νsk
  have hrenΓ : Renames V σ (G.inst νsk) :=
    ⟨hS.fixes, Term.subst νsk, fixesLV_subst V νsk, hS.redo⟩
  have hrenG : Renames V (Term.subst νsk) G :=
    ⟨fixesLV_subst V νsk, σ, hS.fixes, hS.undo⟩
  rw [Model.gEnt_iff]
  simp only [Base.herbrand_brG]
  constructor
  · -- only if: as in Lemma 7, with the single Skolem instance
    intro h
    by_contra hne
    simp only [SimpleEntails, not_exists] at hne
    have hSne : ∀ μ ∈ IMap N H, (H.inst μ \ C.cons (G.inst νsk)).Nonempty := by
      intro μ _
      rw [Set.sdiff_nonempty]
      intro hsub
      apply hne (fun b => σ (μ b))
      rw [← Graph.mapT_inst_of_fixes hS.fixH]
      calc Graph.mapT σ (H.inst μ) ⊆ Graph.mapT σ (C.cons (G.inst νsk)) :=
            Graph.mapT_mono _ hsub
        _ ⊆ C.cons (Graph.mapT σ (G.inst νsk)) := C.cons_map σ _ hrenΓ
        _ = C.cons G := by rw [hS.back]
    have hpair := h {νsk} (by simpa using hνall) (Set.singleton_nonempty _)
      (fun μ => H.inst μ \ C.cons (G.inst νsk)) (fun μ hμ => ⟨hSne μ hμ, Set.sdiff_subset⟩)
    rw [Set.biUnion_singleton, hinst] at hpair
    have hΔlex : (⋃ μ ∈ IMap N H, (H.inst μ \ C.cons (G.inst νsk))) ⊆ Lex N := by
      intro t ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨μ, hμ, ht, -⟩ := ht
      exact Graph.inst_subset_lex hA.hH hμ ht
    obtain ⟨n, hn⟩ := hN
    have hμc : (fun _ : Bn => n) ∈ IMap N H := fun _ _ => hn
    rcases (C.mem_frame_iff hΓlex hΔlex).1 hpair with ⟨t, ht, htc⟩ | ⟨hempty, -⟩
    · simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨μ, -, -, hnot⟩ := ht
      exact hnot htc
    · -- the succedent is not empty: `N` has a name, so `H` has an instance over `N`
      obtain ⟨t, ht⟩ := hSne _ hμc
      have hmem : t ∈ ⋃ μ ∈ IMap N H, (H.inst μ \ C.cons (G.inst νsk)) :=
        Set.mem_biUnion hμc ht
      rw [hempty] at hmem
      exact Set.notMem_empty _ hmem
  · -- if: the witness, pushed through the Skolemization
    rintro ⟨μ₀, hμ₀⟩ x hx hne S hS'
    have hΓeq : (⋃ ν ∈ x, (G.inst νsk).inst ν) = G.inst νsk := by
      obtain ⟨ν₀, hν₀⟩ := hne
      apply Set.Subset.antisymm
      · intro t ht
        simp only [Set.mem_iUnion, exists_prop] at ht
        obtain ⟨ν, -, ht⟩ := ht
        rwa [hinst ν] at ht
      · intro t ht
        have ht' : t ∈ (G.inst νsk).inst ν₀ := by rw [hinst ν₀]; exact ht
        exact Set.mem_biUnion hν₀ ht'
    rw [hΓeq]
    have hΔlex : (⋃ μ ∈ IMap N H, S μ) ⊆ Lex N := by
      intro t ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨μ, hμ, ht⟩ := ht
      exact Graph.inst_subset_lex hA.hH hμ ((hS' μ hμ).2 ht)
    rw [C.mem_frame_iff hΓlex hΔlex]
    left
    have hμ' : (fun b => Term.subst νsk (μ₀ b)) ∈ IMap N H :=
      witness_coordinate' hA (C.terms_cons G) hμ₀ hS.mem
    obtain ⟨b, hb⟩ := (hS' _ hμ').1
    refine ⟨b, Set.mem_biUnion hμ' hb, ?_⟩
    have hb' := (hS' _ hμ').2 hb
    rw [← Graph.inst_inst] at hb'
    have hchain : Graph.inst νsk (H.inst μ₀) ⊆ C.cons (G.inst νsk) :=
      calc Graph.inst νsk (H.inst μ₀) ⊆ Graph.inst νsk (C.cons G) := Graph.inst_mono _ hμ₀
        _ ⊆ C.cons (G.inst νsk) := C.cons_map (Term.subst νsk) G hrenG
    exact hchain hb'

/-- Incoherence: the counterpart of Proposition 2. -/
theorem incoherent_iff_inc {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    (C.base N).herbrand.Incoherent N (G.inst νsk) ↔ C.inc G := by
  have hΓlex : G.inst νsk ⊆ Lex N := Graph.inst_subset_lex hA.hG hS.mem
  have hΓground : (G.inst νsk).Ground :=
    Graph.ground_of_over (G.inst νsk) hA.names ((Graph.subset_lex_iff _).1 hΓlex)
  have hinst : ∀ ν : Bn → Term Iri Lit Bn, (G.inst νsk).inst ν = G.inst νsk :=
    fun ν => Graph.inst_of_ground (G.inst νsk) ν hΓground
  have hνall : νsk ∈ IMap N (G.inst νsk) := IMap_of_ground hΓground νsk
  have hrenΓ : Renames V σ (G.inst νsk) :=
    ⟨hS.fixes, Term.subst νsk, fixesLV_subst V νsk, hS.redo⟩
  have hrenG : Renames V (Term.subst νsk) G :=
    ⟨fixesLV_subst V νsk, σ, hS.fixes, hS.undo⟩
  rw [Model.incoherent_iff]
  simp only [Base.herbrand_brG]
  constructor
  · intro h
    have hpair := h {νsk} (by simpa using hνall) (Set.singleton_nonempty _)
    rw [Set.biUnion_singleton, hinst] at hpair
    rcases (C.mem_frame_iff hΓlex (Set.empty_subset _)).1 hpair with ⟨t, ht, -⟩ | ⟨-, hi⟩
    · exact (Set.notMem_empty _ ht).elim
    · have hi' := C.inc_map σ _ hrenΓ hi
      rwa [hS.back] at hi'
  · intro hi x hx hne
    have hΓeq : (⋃ ν ∈ x, (G.inst νsk).inst ν) = G.inst νsk := by
      obtain ⟨ν₀, hν₀⟩ := hne
      apply Set.Subset.antisymm
      · intro t ht
        simp only [Set.mem_iUnion, exists_prop] at ht
        obtain ⟨ν, -, ht⟩ := ht
        rwa [hinst ν] at ht
      · intro t ht
        have ht' : t ∈ (G.inst νsk).inst ν₀ := by rw [hinst ν₀]; exact ht
        exact Set.mem_biUnion hν₀ ht'
    rw [hΓeq, C.mem_frame_iff hΓlex (Set.empty_subset _)]
    exact Or.inr ⟨rfl, C.inc_map (Term.subst νsk) G hrenG hi⟩

/-- **The general theorem.** For a base presented by `cons` and `inc`, implication in the fit
models from the Skolemization of `G` to `H` is simple entailment from `cons G`. -/
theorem general {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) (hN : N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    FitEnt (C.base N) (G.inst νsk) H ↔ SimpleEntails (C.cons G) H :=
  (recovery (C.base N)
      (Graph.names_subset_of_subset_lex (Graph.inst_subset_lex hA.hG hS.mem)) hA.hH).trans
    (C.witness_characterization hA hN hS)

/-- **The general theorem, part (I).** The right-hand side of `general` mentions neither the
Skolemization nor `N`: the verdict is the same for every admissible nonempty `N` and every
Skolemization (compare `fitEnt_independent_of_N`). -/
theorem general_independent {N' : Set (Term Iri Lit Bn)} {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) (hN : N.Nonempty) (hA' : Admissible N' G H V) (hN' : N'.Nonempty)
    {νsk νsk' : Bn → Term Iri Lit Bn} {σ σ' : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) (hS' : SkolemPair N' V G H νsk' σ') :
    FitEnt (C.base N) (G.inst νsk) H ↔ FitEnt (C.base N') (G.inst νsk') H :=
  (C.general hA hN hS).trans (C.general hA' hN' hS').symm

/-- The general theorem, part (I), for incoherence: the right-hand side of
`incoherent_iff_inc` mentions neither the Skolemization nor `N`. -/
theorem incoherent_independent {N' : Set (Term Iri Lit Bn)} {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) (hA' : Admissible N' G H V)
    {νsk νsk' : Bn → Term Iri Lit Bn} {σ σ' : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) (hS' : SkolemPair N' V G H νsk' σ') :
    (C.base N).herbrand.Incoherent N (G.inst νsk) ↔
      (C.base N').herbrand.Incoherent N' (G.inst νsk') :=
  (C.incoherent_iff_inc hA hS).trans (C.incoherent_iff_inc hA' hS').symm

end ConsBase

/-! ## The regime base without explosion is an instance -/

/-- `cl_R` and `R`-inconsistency as a `ConsBase`.  Its base is `B_R` without explosion. -/
def Regime.consBase (R : Regime Iri Lit Bn V) : ConsBase Iri Lit Bn V where
  cons := R.clPos
  inc := R.Inconsistent
  extensive := R.subset_clPos
  terms_cons := R.terms_clPos_subset
  cons_map := fun _ X h => R.clPos_map h.fixes X
  inc_map := fun _ _ h hi => R.inconsistent_map h.fixes hi

/-- Check against Theorem 2: on an `R`-consistent graph, Definition 11 over the explosive
base `B_R` and the Skolem reading over the non-exploding base give the same verdicts. -/
theorem Regime.fitEnt_skolem_iff (R : Regime Iri Lit Bn V) {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) (hN : N.Nonempty) {νsk : Bn → Term Iri Lit Bn}
    {σ : Term Iri Lit Bn → Term Iri Lit Bn} (hS : SkolemPair N V G H νsk σ)
    (hcons : ¬ R.Inconsistent G) :
    FitEnt (R.base N) G H ↔ FitEnt (R.consBase.base N) (G.inst νsk) H := by
  rw [closure_regimes R hA, R.consBase.general hA hN hS]
  show R.Inconsistent G ∨ SimpleEntails (R.clPos G) H ↔ SimpleEntails (R.clPos G) H
  exact ⟨fun h => h.resolve_left hcons, Or.inr⟩

end ISRDF
