import ISRDF.General

/-!
# Implication-Space Semantics for RDF — one spine for the monotone and the general case

`Semantics.lean` proves Theorem 2 for the base `B_R` of a regime (Definition 11 on both
sides, explosion).  `General.lean` proves the general theorem for a base given by `cons` and
`inc` (Skolem reading of the antecedent, no explosion).  The two proofs share their middle
and are linked only by `Regime.fitEnt_skolem_iff`, on `R`-consistent graphs.

This file makes one chain of them.  It adds declarations only.

* **A ground antecedent is one pair** (`Model.gEnt_ground_iff`,
  `Model.incoherent_ground_iff`): for ground `Γ`, Definition 11 reduces to Definition 10.
* **Definition 11 gives the Skolem reading, in every model**
  (`Model.gEnt_inst_of_gEnt`, `fitEnt_inst_of_fitEnt`): nothing is assumed about the base.
* **The base with or without explosion** (`ConsBase.baseWith e`): `Γ |~ Δ` iff `Δ` meets
  `cons Γ`, or `inc Γ` and (`e` or `Δ = ∅`).  `e := False` is `ConsBase.base`
  (`ConsBase.baseWith_false`); `e := True` at a regime is `B_R` (`Regime.base_eq_baseWith`).
* **The general theorem for both** (`ConsBase.witness_characterization_with`,
  `ConsBase.incoherent_iff_inc_with`, `ConsBase.general_with`).  The hypothesis on `N` is
  `e ∨ N.Nonempty`: with explosion `N` may be empty.
* **The bridge** (`ConsBase.InstMonotone.gEnt_iff_skolem`,
  `ConsBase.InstMonotone.incoherent_iff_skolem`, `ConsBase.InstMonotone.fitEnt_iff_skolem`):
  on a base that is monotone and invariant under instance mappings
  (`ConsBase.InstMonotone`), Definition 11 and the Skolem reading of the antecedent agree.
* **Theorem 2 and Proposition 2 as corollaries** (`closure_regimes_of_general`,
  `incoherence_recovery_of_general`), with the statements of `closure_regimes` and
  `incoherence_recovery`, and proofs that do not use Lemma 7, Proposition 2, Lemma 4 or
  Lemma 5 of `Semantics.lean`.
-/

set_option autoImplicit false

namespace ISRDF

variable {Iri Lit Bn : Type} {V : Set Iri} {N : Set (Term Iri Lit Bn)}

/-! ## A ground antecedent is one pair -/

/-- An instance of `G` over an admissible `N` is ground. -/
theorem Admissible.inst_ground {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    {ν : Bn → Term Iri Lit Bn} (hν : ν ∈ IMap N G) : (G.inst ν).Ground :=
  Graph.ground_of_over (G.inst ν) hA.names
    ((Graph.subset_lex_iff _).1 (Graph.inst_subset_lex hA.hG hν))

namespace Model
variable (M : Model Iri Lit Bn)

/-- Every instance of a ground graph is the graph, so the bearers of a nonempty family of
instances are the bearers of the graph. -/
theorem biUnion_inst_of_ground {Γ : Graph Iri Lit Bn} (hΓ : Γ.Ground)
    {x : Set (Bn → Term Iri Lit Bn)} (hne : x.Nonempty) :
    (⋃ ν ∈ x, M.brG (Γ.inst ν)) = M.brG Γ := by
  obtain ⟨ν₀, hν₀⟩ := hne
  apply Set.Subset.antisymm
  · intro t ht
    simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨ν, -, ht⟩ := ht
    rwa [Graph.inst_of_ground Γ ν hΓ] at ht
  · intro t ht
    have ht' : t ∈ M.brG (Γ.inst ν₀) := by rw [Graph.inst_of_ground Γ ν₀ hΓ]; exact ht
    exact Set.mem_biUnion hν₀ ht'

/-- **A ground antecedent is one pair.**  For ground `Γ`, `⟦Γ⟧ |∼ ⟦H⟧` iff every selection
from the instances of `H` gives a good implication with antecedent `B(Γ)`.  (`ν₀` is any
map; it only witnesses that the family of instance mappings is not empty.) -/
theorem gEnt_ground_iff {Γ H : Graph Iri Lit Bn} (hΓ : Γ.Ground)
    (ν₀ : Bn → Term Iri Lit Bn) :
    M.GEnt N Γ H ↔
      ∀ S : (Bn → Term Iri Lit Bn) → Set (Triple M.Obj),
        (∀ μ ∈ IMap N H, (S μ).Nonempty ∧ S μ ⊆ M.brG (H.inst μ)) →
        (M.brG Γ, ⋃ μ ∈ IMap N H, S μ) ∈ M.I := by
  rw [Model.gEnt_iff]
  constructor
  · intro h S hS
    have hpair := h {ν₀} (Set.singleton_subset_iff.2 (IMap_of_ground hΓ ν₀))
      (Set.singleton_nonempty ν₀) S hS
    rwa [M.biUnion_inst_of_ground hΓ (Set.singleton_nonempty ν₀)] at hpair
  · intro h x _ hne S hS
    rw [M.biUnion_inst_of_ground hΓ hne]
    exact h S hS

/-- A ground antecedent is one pair, for incoherence. -/
theorem incoherent_ground_iff {Γ : Graph Iri Lit Bn} (hΓ : Γ.Ground)
    (ν₀ : Bn → Term Iri Lit Bn) :
    M.Incoherent N Γ ↔ (M.brG Γ, (∅ : Set (Triple M.Obj))) ∈ M.I := by
  rw [Model.incoherent_iff]
  constructor
  · intro h
    have hpair := h {ν₀} (Set.singleton_subset_iff.2 (IMap_of_ground hΓ ν₀))
      (Set.singleton_nonempty ν₀)
    rwa [M.biUnion_inst_of_ground hΓ (Set.singleton_nonempty ν₀)] at hpair
  · intro h x _ hne
    rw [M.biUnion_inst_of_ground hΓ hne]
    exact h

/-! ## Definition 11 gives the Skolem reading, in every model -/

/-- If `⟦G⟧ |∼ ⟦H⟧` with `G` read by Definition 11, then `⟦ν(G)⟧ |∼ ⟦H⟧` for every ground
instance `ν(G)` over `N`: the family of Definition 11 contains the singleton `{ν}`.  Nothing
is assumed about the model. -/
theorem gEnt_inst_of_gEnt {G H : Graph Iri Lit Bn} {ν : Bn → Term Iri Lit Bn}
    (hν : ν ∈ IMap N G) (hΓ : (G.inst ν).Ground) (h : M.GEnt N G H) :
    M.GEnt N (G.inst ν) H := by
  rw [M.gEnt_ground_iff hΓ ν]
  intro S hS
  have hpair := (M.gEnt_iff).1 h {ν} (Set.singleton_subset_iff.2 hν)
    (Set.singleton_nonempty ν) S hS
  rwa [Set.biUnion_singleton] at hpair

/-- The same for incoherence. -/
theorem incoherent_inst_of_incoherent {G : Graph Iri Lit Bn} {ν : Bn → Term Iri Lit Bn}
    (hν : ν ∈ IMap N G) (hΓ : (G.inst ν).Ground) (h : M.Incoherent N G) :
    M.Incoherent N (G.inst ν) := by
  rw [M.incoherent_ground_iff hΓ ν]
  have hpair := (M.incoherent_iff).1 h {ν} (Set.singleton_subset_iff.2 hν)
    (Set.singleton_nonempty ν)
  rwa [Set.biUnion_singleton] at hpair

end Model

/-- Definition 11 never grants what the Skolem reading denies: for every base, implication
in the fit models from `G` gives implication from each ground instance of `G`. -/
theorem fitEnt_inst_of_fitEnt (B : Base N) {G H : Graph Iri Lit Bn}
    {ν : Bn → Term Iri Lit Bn} (hν : ν ∈ IMap N G) (hΓ : (G.inst ν).Ground)
    (h : FitEnt B G H) : FitEnt B (G.inst ν) H :=
  fun M hM => M.gEnt_inst_of_gEnt hν hΓ (h M hM)

/-! ## The base with or without explosion -/

/-- Two bases with the same relation are the same base. -/
theorem Base.ext_rel {B B' : Base N} (h : ∀ Γ Δ, B.rel Γ Δ ↔ B'.rel Γ Δ) : B = B' := by
  obtain ⟨r, c⟩ := B
  obtain ⟨r', c'⟩ := B'
  have hr : r = r' := by
    funext Γ Δ
    exact propext (h Γ Δ)
  subst hr
  rfl

namespace ConsBase
variable (C : ConsBase Iri Lit Bn V)

/-- The base of a `ConsBase`, exploding when `e` holds: `Δ` meets `Cons(Γ)`, or `Γ` is
incoherent and either `e` or `Δ = ∅`. -/
def baseWith (e : Prop) (N : Set (Term Iri Lit Bn)) : Base N where
  rel Γ Δ := (Δ ∩ C.cons Γ).Nonempty ∨ (C.inc Γ ∧ (e ∨ Δ = ∅))
  containment := fun Γ _ _ _ ⟨t, ht, ht'⟩ => Or.inl ⟨t, ht', C.extensive Γ ht⟩

/-- Without explosion it is `ConsBase.base`. -/
theorem baseWith_false : C.baseWith False N = C.base N :=
  Base.ext_rel fun Γ Δ => by
    show ((Δ ∩ C.cons Γ).Nonempty ∨ (C.inc Γ ∧ (False ∨ Δ = ∅))) ↔
      ((Δ ∩ C.cons Γ).Nonempty ∨ (Δ = ∅ ∧ C.inc Γ))
    constructor
    · rintro (h | ⟨hi, hf | he⟩)
      · exact Or.inl h
      · exact hf.elim
      · exact Or.inr ⟨he, hi⟩
    · rintro (h | ⟨he, hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hi, Or.inr he⟩

theorem mem_frame_with_iff {e : Prop} {Γ Δ : Graph Iri Lit Bn} (hΓ : Γ ⊆ Lex N)
    (hΔ : Δ ⊆ Lex N) :
    (Γ, Δ) ∈ (C.baseWith e N).frame ↔
      (Δ ∩ C.cons Γ).Nonempty ∨ (C.inc Γ ∧ (e ∨ Δ = ∅)) :=
  ⟨(C.baseWith e N).rel_of_mem_frame hΓ hΔ, (C.baseWith e N).mem_frame_of_rel hΓ hΔ⟩

/-! ## The general theorem, with or without explosion -/

/-- **The general theorem in the Herbrand model, with or without explosion.**  The
counterpart of Lemma 7 for the Skolem reading of the antecedent.  With explosion (`e`) the
right-hand side gains the disjunct `inc G` and `N` may be empty; without it `N` must be
nonempty. -/
theorem witness_characterization_with {e : Prop} {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) (hN : e ∨ N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    (C.baseWith e N).herbrand.GEnt N (G.inst νsk) H ↔
      (e ∧ C.inc G) ∨ SimpleEntails (C.cons G) H := by
  have hΓlex : G.inst νsk ⊆ Lex N := Graph.inst_subset_lex hA.hG hS.mem
  have hΓground : (G.inst νsk).Ground := hA.inst_ground hS.mem
  have hrenΓ : Renames V σ (G.inst νsk) :=
    ⟨hS.fixes, Term.subst νsk, fixesLV_subst V νsk, hS.redo⟩
  have hrenG : Renames V (Term.subst νsk) G :=
    ⟨fixesLV_subst V νsk, σ, hS.fixes, hS.undo⟩
  rw [Model.gEnt_ground_iff _ hΓground νsk]
  simp only [Base.herbrand_brG]
  constructor
  · -- only if: select, from each instance of `H`, what lies outside the consequences
    intro h
    by_contra hne
    rw [not_or] at hne
    obtain ⟨hnotinc, hnowit⟩ := hne
    simp only [SimpleEntails, not_exists] at hnowit
    have hback : C.inc (G.inst νsk) → C.inc G := by
      intro hi
      have hi' := C.inc_map σ _ hrenΓ hi
      rwa [hS.back] at hi'
    have hSne : ∀ μ ∈ IMap N H, (H.inst μ \ C.cons (G.inst νsk)).Nonempty := by
      intro μ _
      rw [Set.sdiff_nonempty]
      intro hsub
      apply hnowit (fun b => σ (μ b))
      rw [← Graph.mapT_inst_of_fixes hS.fixH]
      calc Graph.mapT σ (H.inst μ) ⊆ Graph.mapT σ (C.cons (G.inst νsk)) :=
            Graph.mapT_mono _ hsub
        _ ⊆ C.cons (Graph.mapT σ (G.inst νsk)) := C.cons_map σ _ hrenΓ
        _ = C.cons G := by rw [hS.back]
    have hpair := h (fun μ => H.inst μ \ C.cons (G.inst νsk))
      (fun μ hμ => ⟨hSne μ hμ, Set.sdiff_subset⟩)
    have hΔlex : (⋃ μ ∈ IMap N H, (H.inst μ \ C.cons (G.inst νsk))) ⊆ Lex N := by
      intro t ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨μ, hμ, ht, -⟩ := ht
      exact Graph.inst_subset_lex hA.hH hμ ht
    rcases (C.mem_frame_with_iff hΓlex hΔlex).1 hpair with ⟨t, ht, htc⟩ | ⟨hi, he | hempty⟩
    · -- the selection avoids the consequences
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨μ, -, -, hnot⟩ := ht
      exact hnot htc
    · -- explosion: incoherence travels back along `σ`
      exact hnotinc ⟨he, hback hi⟩
    · -- no explosion: the succedent is not empty, because `N` has a name
      rcases hN with he | ⟨n, hn⟩
      · exact hnotinc ⟨he, hback hi⟩
      · have hμc : (fun _ : Bn => n) ∈ IMap N H := fun _ _ => hn
        obtain ⟨t, ht⟩ := hSne _ hμc
        have hmem : t ∈ ⋃ μ ∈ IMap N H, (H.inst μ \ C.cons (G.inst νsk)) :=
          Set.mem_biUnion hμc ht
        rw [hempty] at hmem
        exact Set.notMem_empty _ hmem
  · -- if
    intro h S hS'
    have hΔlex : (⋃ μ ∈ IMap N H, S μ) ⊆ Lex N := by
      intro t ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨μ, hμ, ht⟩ := ht
      exact Graph.inst_subset_lex hA.hH hμ ((hS' μ hμ).2 ht)
    rw [C.mem_frame_with_iff hΓlex hΔlex]
    rcases h with ⟨he, hi⟩ | ⟨μ₀, hμ₀⟩
    · -- explosion: incoherence travels forward along the Skolemization
      exact Or.inr ⟨C.inc_map (Term.subst νsk) G hrenG hi, Or.inl he⟩
    · -- the witness, pushed through the Skolemization
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

/-- **Incoherence, with or without explosion.**  The counterpart of Proposition 2.  The flag
makes no difference: the succedent is empty. -/
theorem incoherent_iff_inc_with {e : Prop} {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) {νsk : Bn → Term Iri Lit Bn}
    {σ : Term Iri Lit Bn → Term Iri Lit Bn} (hS : SkolemPair N V G H νsk σ) :
    (C.baseWith e N).herbrand.Incoherent N (G.inst νsk) ↔ C.inc G := by
  have hΓlex : G.inst νsk ⊆ Lex N := Graph.inst_subset_lex hA.hG hS.mem
  have hΓground : (G.inst νsk).Ground := hA.inst_ground hS.mem
  have hrenΓ : Renames V σ (G.inst νsk) :=
    ⟨hS.fixes, Term.subst νsk, fixesLV_subst V νsk, hS.redo⟩
  have hrenG : Renames V (Term.subst νsk) G :=
    ⟨fixesLV_subst V νsk, σ, hS.fixes, hS.undo⟩
  rw [Model.incoherent_ground_iff _ hΓground νsk]
  simp only [Base.herbrand_brG]
  rw [C.mem_frame_with_iff hΓlex (Set.empty_subset _)]
  constructor
  · rintro (⟨t, ht, -⟩ | ⟨hi, -⟩)
    · exact (Set.notMem_empty _ ht).elim
    · have hi' := C.inc_map σ _ hrenΓ hi
      rwa [hS.back] at hi'
  · intro hi
    exact Or.inr ⟨C.inc_map (Term.subst νsk) G hrenG hi, Or.inr rfl⟩

/-- **The general theorem, with or without explosion.** -/
theorem general_with {e : Prop} {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    (hN : e ∨ N.Nonempty) {νsk : Bn → Term Iri Lit Bn}
    {σ : Term Iri Lit Bn → Term Iri Lit Bn} (hS : SkolemPair N V G H νsk σ) :
    FitEnt (C.baseWith e N) (G.inst νsk) H ↔ (e ∧ C.inc G) ∨ SimpleEntails (C.cons G) H :=
  (recovery (C.baseWith e N)
      (Graph.names_subset_of_subset_lex (Graph.inst_subset_lex hA.hG hS.mem)) hA.hH).trans
    (C.witness_characterization_with hA hN hS)

/-! The three results of `General.lean` are the case without explosion. -/

/-- `ConsBase.witness_characterization` from the flagged form. -/
theorem witness_characterization_of_with {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    (hN : N.Nonempty) {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    (C.base N).herbrand.GEnt N (G.inst νsk) H ↔ SimpleEntails (C.cons G) H := by
  rw [← C.baseWith_false]
  exact (C.witness_characterization_with hA (Or.inr hN) hS).trans
    ⟨fun h => h.resolve_left fun h' => h'.1, Or.inr⟩

/-- `ConsBase.incoherent_iff_inc` from the flagged form. -/
theorem incoherent_iff_inc_of_with {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    (C.base N).herbrand.Incoherent N (G.inst νsk) ↔ C.inc G := by
  rw [← C.baseWith_false]
  exact C.incoherent_iff_inc_with hA hS

/-- `ConsBase.general` from the flagged form. -/
theorem general_of_with {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) (hN : N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    FitEnt (C.base N) (G.inst νsk) H ↔ SimpleEntails (C.cons G) H := by
  rw [← C.baseWith_false]
  exact (C.general_with hA (Or.inr hN) hS).trans
    ⟨fun h => h.resolve_left fun h' => h'.1, Or.inr⟩

/-! ## The bridge: Definition 11 and the Skolem reading on monotone bases -/

/-- A base is monotone and invariant under instance mappings: `cons` and `inc` are monotone,
and both are preserved by every substitution of terms for blank nodes (which may merge
terms).  Regimes have these properties; a base with defeaters in general has neither. -/
structure InstMonotone : Prop where
  cons_mono : ∀ {X Y : Graph Iri Lit Bn}, X ⊆ Y → C.cons X ⊆ C.cons Y
  inc_mono : ∀ {X Y : Graph Iri Lit Bn}, X ⊆ Y → C.inc X → C.inc Y
  cons_inst : ∀ (ν : Bn → Term Iri Lit Bn) (X : Graph Iri Lit Bn),
    (C.cons X).inst ν ⊆ C.cons (X.inst ν)
  inc_inst : ∀ (ν : Bn → Term Iri Lit Bn) (X : Graph Iri Lit Bn), C.inc X → C.inc (X.inst ν)

variable {C}

/-- On a monotone base the right-hand side of the general theorem gives `⟦G⟧ |∼ ⟦H⟧` with
`G` read by Definition 11.  This is the "if" half of Lemma 7.  It needs no Skolemization and
no assumption on `N` beyond admissibility. -/
theorem InstMonotone.gEnt_of_cons {e : Prop} (hM : C.InstMonotone) {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) (h : (e ∧ C.inc G) ∨ SimpleEntails (C.cons G) H) :
    (C.baseWith e N).herbrand.GEnt N G H := by
  rw [Model.gEnt_iff]
  simp only [Base.herbrand_brG]
  intro x hx hne S hS
  have hΓlex : (⋃ ν ∈ x, G.inst ν) ⊆ Lex N := by
    intro t ht
    simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨ν, hν, ht⟩ := ht
    exact Graph.inst_subset_lex hA.hG (hx hν) ht
  have hΔlex : (⋃ μ ∈ IMap N H, S μ) ⊆ Lex N := by
    intro t ht
    simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨μ, hμ, ht⟩ := ht
    exact Graph.inst_subset_lex hA.hH hμ ((hS μ hμ).2 ht)
  rw [C.mem_frame_with_iff hΓlex hΔlex]
  obtain ⟨ν₀, hν₀⟩ := hne
  have hsub : G.inst ν₀ ⊆ ⋃ ν ∈ x, G.inst ν :=
    Set.subset_biUnion_of_mem (u := fun ν => G.inst ν) hν₀
  rcases h with ⟨he, hi⟩ | ⟨μ₀, hμ₀⟩
  · exact Or.inr ⟨hM.inc_mono hsub (hM.inc_inst ν₀ G hi), Or.inl he⟩
  · left
    have hμ' := witness_coordinate' hA (C.terms_cons G) hμ₀ (hx hν₀)
    obtain ⟨b, hb⟩ := (hS _ hμ').1
    refine ⟨b, Set.mem_biUnion hμ' hb, ?_⟩
    have hb' := (hS _ hμ').2 hb
    rw [← Graph.inst_inst] at hb'
    have hchain : Graph.inst ν₀ (H.inst μ₀) ⊆ C.cons (⋃ ν ∈ x, G.inst ν) :=
      calc Graph.inst ν₀ (H.inst μ₀) ⊆ Graph.inst ν₀ (C.cons G) := Graph.inst_mono _ hμ₀
        _ ⊆ C.cons (G.inst ν₀) := hM.cons_inst ν₀ G
        _ ⊆ C.cons (⋃ ν ∈ x, G.inst ν) := hM.cons_mono hsub
    exact hchain hb'

/-- On a monotone base an incoherent `G` has an incoherent content under Definition 11.
The "if" half of Proposition 2. -/
theorem InstMonotone.incoherent_of_inc {e : Prop} (hM : C.InstMonotone)
    {G : Graph Iri Lit Bn} (hG : G.names ⊆ N) (hi : C.inc G) :
    (C.baseWith e N).herbrand.Incoherent N G := by
  rw [Model.incoherent_iff]
  simp only [Base.herbrand_brG]
  intro x hx hne
  have hΓlex : (⋃ ν ∈ x, G.inst ν) ⊆ Lex N := by
    intro t ht
    simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨ν, hν, ht⟩ := ht
    exact Graph.inst_subset_lex hG (hx hν) ht
  rw [C.mem_frame_with_iff hΓlex (Set.empty_subset _)]
  obtain ⟨ν₀, hν₀⟩ := hne
  exact Or.inr ⟨hM.inc_mono (Set.subset_biUnion_of_mem (u := fun ν => G.inst ν) hν₀)
    (hM.inc_inst ν₀ G hi), Or.inr rfl⟩

/-- **The bridge, in the Herbrand model.**  On a monotone base, reading the antecedent by
Definition 11 and reading it through its Skolemization give the same verdict.  From left to
right nothing about the base is used (`Model.gEnt_inst_of_gEnt`). -/
theorem InstMonotone.gEnt_iff_skolem {e : Prop} (hM : C.InstMonotone)
    {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) (hN : e ∨ N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    (C.baseWith e N).herbrand.GEnt N G H ↔
      (C.baseWith e N).herbrand.GEnt N (G.inst νsk) H :=
  ⟨Model.gEnt_inst_of_gEnt _ hS.mem (hA.inst_ground hS.mem),
   fun h => hM.gEnt_of_cons hA ((C.witness_characterization_with hA hN hS).1 h)⟩

/-- The bridge for incoherence. -/
theorem InstMonotone.incoherent_iff_skolem {e : Prop} (hM : C.InstMonotone)
    {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) {νsk : Bn → Term Iri Lit Bn}
    {σ : Term Iri Lit Bn → Term Iri Lit Bn} (hS : SkolemPair N V G H νsk σ) :
    (C.baseWith e N).herbrand.Incoherent N G ↔
      (C.baseWith e N).herbrand.Incoherent N (G.inst νsk) :=
  ⟨Model.incoherent_inst_of_incoherent _ hS.mem (hA.inst_ground hS.mem),
   fun h => hM.incoherent_of_inc hA.hG ((C.incoherent_iff_inc_with hA hS).1 h)⟩

/-- **The bridge, in the fit models.** -/
theorem InstMonotone.fitEnt_iff_skolem {e : Prop} (hM : C.InstMonotone)
    {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) (hN : e ∨ N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    FitEnt (C.baseWith e N) G H ↔ FitEnt (C.baseWith e N) (G.inst νsk) H :=
  (recovery (C.baseWith e N) hA.hG hA.hH).trans
    ((hM.gEnt_iff_skolem hA hN hS).trans
      (recovery (C.baseWith e N)
        (Graph.names_subset_of_subset_lex (Graph.inst_subset_lex hA.hG hS.mem)) hA.hH).symm)

/-- **The general theorem with Definition 11 in antecedent position**, for a monotone base:
`G ⊨ H` in the fit models iff (`e` and `G` is incoherent) or `Cons(G)` simply entails `H`.
Theorem 2 is the case of a regime with `e := True`. -/
theorem InstMonotone.general_def11 {e : Prop} (hM : C.InstMonotone)
    {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) (hN : e ∨ N.Nonempty) :
    FitEnt (C.baseWith e N) G H ↔ (e ∧ C.inc G) ∨ SimpleEntails (C.cons G) H := by
  obtain ⟨νsk, σ, hS⟩ := exists_skolemPair hA
  exact (hM.fitEnt_iff_skolem hA hN hS).trans (C.general_with hA hN hS)

/-- Proposition 2 with Definition 11, for a monotone base. -/
theorem InstMonotone.incoherent_def11 {e : Prop} (hM : C.InstMonotone)
    {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) :
    (C.baseWith e N).herbrand.Incoherent N G ↔ C.inc G := by
  obtain ⟨νsk, σ, hS⟩ := exists_skolemPair hA
  exact (hM.incoherent_iff_skolem hA hS).trans (C.incoherent_iff_inc_with hA hS)

end ConsBase

/-! ## Theorem 2 and Proposition 2 as corollaries -/

namespace Regime
variable (R : Regime Iri Lit Bn V)

/-- The base of a regime is monotone and invariant under instance mappings. -/
theorem consBase_instMonotone : R.consBase.InstMonotone where
  cons_mono := fun h => R.clPos_mono h
  inc_mono := fun h hi => R.inconsistent_mono h hi
  cons_inst := fun ν X => R.clPos_map (fixesLV_subst V ν) X
  inc_inst := fun ν _ hi => R.inconsistent_map (fixesLV_subst V ν) hi

/-- `B_R` is the exploding base of `cl_R` and `R`-inconsistency. -/
theorem base_eq_baseWith : R.base N = R.consBase.baseWith True N :=
  Base.ext_rel fun Γ Δ => by
    show (R.Inconsistent Γ ∨ (Δ ∩ R.clPos Γ).Nonempty) ↔
      ((Δ ∩ R.clPos Γ).Nonempty ∨ (R.Inconsistent Γ ∧ (True ∨ Δ = ∅)))
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨h, Or.inl trivial⟩
      · exact Or.inl h
    · rintro (h | ⟨h, -⟩)
      · exact Or.inr h
      · exact Or.inl h

/-- `Regime.fitEnt_skolem_iff` without its consistency hypothesis: over `B_R` itself,
Definition 11 and the Skolem reading of the antecedent agree on every graph. -/
theorem fitEnt_iff_skolem {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    FitEnt (R.base N) G H ↔ FitEnt (R.base N) (G.inst νsk) H := by
  rw [R.base_eq_baseWith]
  exact R.consBase_instMonotone.fitEnt_iff_skolem hA (Or.inl trivial) hS

end Regime

/-- **Theorem 2 (Closure regimes), from the general theorem.**  The statement of
`closure_regimes`; the proof is Theorem 1, the bridge and the general theorem with
explosion.  It does not use Lemma 7 (`witness_characterization`), Lemma 4
(`witness_coordinate`) or Lemma 5 (`skolemization`) of `Semantics.lean`. -/
theorem closure_regimes_of_general (R : Regime Iri Lit Bn V) {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) : FitEnt (R.base N) G H ↔ R.Entails G H := by
  rw [R.base_eq_baseWith]
  refine (R.consBase_instMonotone.general_def11 (e := True) hA (Or.inl trivial)).trans ?_
  show (True ∧ R.Inconsistent G) ∨ SimpleEntails (R.clPos G) H ↔
    R.Inconsistent G ∨ SimpleEntails (R.clPos G) H
  rw [true_and]

/-- **Proposition 2 (Incoherence recovery), from the general theorem.**  The statement of
`incoherence_recovery`. -/
theorem incoherence_recovery_of_general (R : Regime Iri Lit Bn V) {G : Graph Iri Lit Bn}
    (hA : Admissible N G ∅ V) : (R.base N).herbrand.Incoherent N G ↔ R.Inconsistent G := by
  rw [R.base_eq_baseWith]
  exact R.consBase_instMonotone.incoherent_def11 (e := True) hA

/-! ## The older lemmas as special cases -/

/-- Lemma 4 (`witness_coordinate`) is `witness_coordinate'` at `X = cl_R(G) \ {⊥}`. -/
theorem witness_coordinate_of_general (R : Regime Iri Lit Bn V) {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H V) {μ₀ : Bn → Term Iri Lit Bn} (hμ₀ : H.inst μ₀ ⊆ R.clPos G)
    {ν₀ : Bn → Term Iri Lit Bn} (hν₀ : ν₀ ∈ IMap N G) :
    (fun b => Term.subst ν₀ (μ₀ b)) ∈ IMap N H :=
  witness_coordinate' hA (R.terms_clPos_subset G) hμ₀ hν₀

/-- Lemma 5 (`skolemization`) is `exists_skolemPair` without the two round trips. -/
theorem skolemization_of_skolemPair {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) :
    ∃ (νsk : Bn → Term Iri Lit Bn) (σ : Term Iri Lit Bn → Term Iri Lit Bn),
      νsk ∈ IMap N G ∧ FixesLV V σ ∧ Graph.mapT σ (G.inst νsk) = G ∧
      (∀ t ∈ H, ∀ x ∈ t.terms, σ x = x) := by
  obtain ⟨νsk, σ, hS⟩ := exists_skolemPair hA
  exact ⟨νsk, σ, hS.mem, hS.fixes, hS.back, hS.fixH⟩

end ISRDF
