import ISRDF.General

/-!
# Implication-Space Semantics for RDF — Part 4: bases with defeasible entries

The base of the nonmonotone case: a regime `R` together with single-conclusion entries
`⟨A, c; E⟩` (premises `A`, conclusion `c` or `⊥`, defeaters `E`).  For a set of triples `Γ`
whose terms are read as constants,

* `K = cl_R(Γ) \ {⊥}`;
* an entry applies at `K` when its premises are in `K` and no defeater is contained in `K`;
* `D*` is the set of conclusions of the applying entries (one round, pooled: entries never
  see each other's conclusions);
* `Cons(Γ) = cl_R(K ∪ D*) \ {⊥}`;
* `Γ` is incoherent iff `R` derives `⊥` from `Γ` or an incompatibility entry applies at `K`.

The construction is in two layers.

**Layer 1** (`DefaultStep`, `Regime.consBaseOf`).  One round of defaults as an arbitrary
function `dstar` of the closure, with an incompatibility predicate `incompat`, assumed only
to introduce no new terms and to be invariant under renamings.  Any such step over any
regime gives a `ConsBase`, so the general theorem applies.  Nothing is assumed monotone.

**Layer 2** (`Entry`, `Entries`, `Entries.step`).  Ground entries, with a closure condition
stated for renaming pairs only.  Closing under all maps fixing `L ∪ V`, as `Regime.uniform`
does, would be wrong here: defeat is not preserved by maps that merge terms.

* Lemma A is `Regime.entriesBase`: the entries base is a `ConsBase`.
* `Regime.entries_general`, `Regime.entries_incoherent_iff`: the general theorem at the
  entries base.
* Property 1 (defeat witness) is `Regime.defeat_witness`.
* Its counterpart for incoherence (lost incoherence) is `Regime.incoherence_witness`.
* Property 2 (materialization) is `Regime.consBaseOf_cons_union` and
  `Regime.consBaseOf_inc_union`, proved at layer 1.
-/

set_option autoImplicit false

namespace ISRDF

variable {Iri Lit Bn : Type} {V : Set Iri}

/-! ## Renamings and the closure -/

theorem Graph.terms_union (X Y : Graph Iri Lit Bn) : (X ∪ Y).terms = X.terms ∪ Y.terms := by
  ext x
  constructor
  · rintro ⟨t, ht | ht, hx⟩
    · exact Or.inl ⟨t, ht, hx⟩
    · exact Or.inr ⟨t, ht, hx⟩
  · rintro (⟨t, ht, hx⟩ | ⟨t, ht, hx⟩)
    · exact ⟨t, Or.inl ht, hx⟩
    · exact ⟨t, Or.inr ht, hx⟩

theorem Graph.mapT_union (f : Term Iri Lit Bn → Term Iri Lit Bn) (X Y : Graph Iri Lit Bn) :
    Graph.mapT f (X ∪ Y) = Graph.mapT f X ∪ Graph.mapT f Y :=
  Set.image_union _ _ _

/-- A renaming of `Y` is a renaming of any graph whose terms come from `Y` and `V`. -/
theorem Renames.of_terms_subset {ρ : Term Iri Lit Bn → Term Iri Lit Bn}
    {X Y : Graph Iri Lit Bn} (h : Renames V ρ Y)
    (hXY : X.terms ⊆ Y.terms ∪ ((fun v => Term.iri v) '' V)) : Renames V ρ X := by
  obtain ⟨ρ', hρ', hinv⟩ := h.inv
  refine ⟨h.fixes, ρ', hρ', ?_⟩
  intro t ht x hx
  rcases hXY ⟨t, ht, hx⟩ with ⟨t', ht', hx'⟩ | ⟨v, hv, hveq⟩
  · exact hinv t' ht' x hx'
  · rw [← hveq]
    show ρ' (ρ (Term.iri v)) = Term.iri v
    rw [h.fixes.2 v hv, hρ'.2 v hv]

namespace Regime
variable (R : Regime Iri Lit Bn V)

/-- A renaming of `X` is a renaming of `cl_R(X)`. -/
theorem renames_clPos {ρ : Term Iri Lit Bn → Term Iri Lit Bn} {X : Graph Iri Lit Bn}
    (h : Renames V ρ X) : Renames V ρ (R.clPos X) :=
  h.of_terms_subset (R.terms_clPos_subset X)

/-- Lemma 6 (Uniformity of closure) with equality: a renaming commutes with the closure.
For an arbitrary map fixing `L ∪ V` only the inclusion `clPos_map` holds. -/
theorem mapT_clPos {ρ : Term Iri Lit Bn → Term Iri Lit Bn} {X : Graph Iri Lit Bn}
    (h : Renames V ρ X) : Graph.mapT ρ (R.clPos X) = R.clPos (Graph.mapT ρ X) := by
  apply Set.Subset.antisymm (R.clPos_map h.fixes X)
  obtain ⟨ρ', hρ', hinv⟩ := h.inv
  intro t ht
  have hback : Graph.mapT ρ' (Graph.mapT ρ X) = X := by
    rw [Graph.mapT_mapT]
    exact Graph.mapT_eq_self X (fun t ht x hx => hinv t ht x hx)
  have ht' : Triple.map ρ' t ∈ R.clPos (Graph.mapT ρ' (Graph.mapT ρ X)) :=
    R.clPos_map hρ' _ ⟨t, ht, rfl⟩
  rw [hback] at ht'
  refine ⟨Triple.map ρ' t, ht', ?_⟩
  rw [Triple.map_map]
  apply Triple.map_eq_self
  intro x hx
  rcases R.terms_clPos_subset (Graph.mapT ρ X) ⟨t, ht, hx⟩ with
    ⟨u, ⟨s, hs, hsu⟩, hxu⟩ | ⟨v, hv, hveq⟩
  · rw [← hsu] at hxu
    obtain ⟨y, hy, hyx⟩ := (Triple.mem_terms_map _ _).1 hxu
    rw [← hyx]
    show ρ (ρ' (ρ y)) = ρ y
    rw [hinv s hs y hy]
  · rw [← hveq]
    show ρ (ρ' (Term.iri v)) = Term.iri v
    rw [hρ'.2 v hv, h.fixes.2 v hv]

/-- Materializing consequences does not change the closure. -/
theorem clPos_union_of_subset {X T : Graph Iri Lit Bn} (hT : T ⊆ R.clPos X) :
    R.clPos (X ∪ T) = R.clPos X := by
  apply Set.Subset.antisymm
  · intro t ht
    exact R.cl_clPos (R.cl_mono (Set.union_subset (R.subset_clPos X) hT) ht)
  · exact R.clPos_mono Set.subset_union_left

/-- Materializing consequences does not change `R`-consistency. -/
theorem inconsistent_union_iff {X T : Graph Iri Lit Bn} (hT : T ⊆ R.clPos X) :
    R.Inconsistent (X ∪ T) ↔ R.Inconsistent X :=
  ⟨fun h => R.cl_clPos (R.cl_mono (Set.union_subset (R.subset_clPos X) hT) h),
    R.inconsistent_mono Set.subset_union_left⟩

end Regime

/-! ## Layer 1: one round of defaults, abstractly -/

/-- One round of defaults, as a function of the closure `K = cl_R(Γ) \ {⊥}`. -/
structure DefaultStep (Iri Lit Bn : Type) (V : Set Iri) where
  /-- `D*`: the default conclusions drawn at `K`. -/
  dstar : Graph Iri Lit Bn → Graph Iri Lit Bn
  /-- An incompatibility entry applies at `K`. -/
  incompat : Graph Iri Lit Bn → Prop
  /-- No new terms. -/
  terms_dstar : ∀ K : Graph Iri Lit Bn,
    (dstar K).terms ⊆ K.terms ∪ ((fun v => Term.iri v) '' V)
  /-- Invariance of `D*` under renamings. -/
  dstar_map : ∀ (ρ : Term Iri Lit Bn → Term Iri Lit Bn) (K : Graph Iri Lit Bn),
    Renames V ρ K → Graph.mapT ρ (dstar K) ⊆ dstar (Graph.mapT ρ K)
  /-- Invariance of incompatibility under renamings. -/
  incompat_map : ∀ (ρ : Term Iri Lit Bn → Term Iri Lit Bn) (K : Graph Iri Lit Bn),
    Renames V ρ K → incompat K → incompat (Graph.mapT ρ K)

/-- The step with no defaults and no incompatibilities. -/
def DefaultStep.empty : DefaultStep Iri Lit Bn V where
  dstar _ := ∅
  incompat _ := False
  terms_dstar _ := by
    rintro x ⟨t, ht, -⟩
    exact (Set.notMem_empty _ ht).elim
  dstar_map _ _ _ := by
    rintro _ ⟨t, ht, -⟩
    exact (Set.notMem_empty _ ht).elim
  incompat_map _ _ _ h := h

/-- The base of a regime with one round of defaults:
`Cons(X) = cl_R(cl_R(X) ∪ D*(cl_R(X)))`, and `X` is incoherent iff `R` derives `⊥` from `X`
or an incompatibility applies at `cl_R(X)`.  It is a `ConsBase`. -/
def Regime.consBaseOf (R : Regime Iri Lit Bn V) (D : DefaultStep Iri Lit Bn V) :
    ConsBase Iri Lit Bn V where
  cons X := R.clPos (R.clPos X ∪ D.dstar (R.clPos X))
  inc X := R.Inconsistent X ∨ D.incompat (R.clPos X)
  extensive X := fun _ ht => R.subset_clPos _ (Or.inl (R.subset_clPos X ht))
  terms_cons X := by
    intro x hx
    rcases R.terms_clPos_subset _ hx with h | h
    · rw [Graph.terms_union] at h
      rcases h with h | h
      · exact R.terms_clPos_subset X h
      · rcases D.terms_dstar _ h with h | h
        · exact R.terms_clPos_subset X h
        · exact Or.inr h
    · exact Or.inr h
  cons_map ρ X h := by
    have hK : Renames V ρ (R.clPos X) := R.renames_clPos h
    calc Graph.mapT ρ (R.clPos (R.clPos X ∪ D.dstar (R.clPos X)))
        ⊆ R.clPos (Graph.mapT ρ (R.clPos X ∪ D.dstar (R.clPos X))) := R.clPos_map h.fixes _
      _ ⊆ R.clPos (R.clPos (Graph.mapT ρ X) ∪ D.dstar (R.clPos (Graph.mapT ρ X))) := by
          apply R.clPos_mono
          rw [Graph.mapT_union, ← R.mapT_clPos h]
          exact Set.union_subset_union_right _ (D.dstar_map ρ _ hK)
  inc_map ρ X h := by
    rintro (hi | hi)
    · exact Or.inl (R.inconsistent_map h.fixes hi)
    · right
      rw [← R.mapT_clPos h]
      exact D.incompat_map ρ _ (R.renames_clPos h) hi

namespace Regime
variable (R : Regime Iri Lit Bn V) (D : DefaultStep Iri Lit Bn V)

theorem consBaseOf_cons (X : Graph Iri Lit Bn) :
    (R.consBaseOf D).cons X = R.clPos (R.clPos X ∪ D.dstar (R.clPos X)) := rfl

theorem consBaseOf_inc (X : Graph Iri Lit Bn) :
    (R.consBaseOf D).inc X ↔ R.Inconsistent X ∨ D.incompat (R.clPos X) := Iff.rfl

/-- With no defaults, `Cons` is `cl_R`: the regime base without explosion. -/
theorem consBaseOf_empty_cons (X : Graph Iri Lit Bn) :
    (R.consBaseOf DefaultStep.empty).cons X = R.clPos X := by
  show R.clPos (R.clPos X ∪ ∅) = R.clPos X
  rw [Set.union_empty]
  exact Set.Subset.antisymm (fun _ ht => R.cl_clPos ht) (R.subset_clPos _)

/-- With no incompatibilities, incoherence is `R`-inconsistency. -/
theorem consBaseOf_empty_inc (X : Graph Iri Lit Bn) :
    (R.consBaseOf DefaultStep.empty).inc X ↔ R.Inconsistent X :=
  ⟨fun h => h.resolve_right (fun hf => hf), Or.inl⟩

/-- **Property 2 (Materialization)**, consequence: adding triples already in `cl_R(X)`
changes no consequence. -/
theorem consBaseOf_cons_union {X T : Graph Iri Lit Bn} (hT : T ⊆ R.clPos X) :
    (R.consBaseOf D).cons (X ∪ T) = (R.consBaseOf D).cons X := by
  rw [consBaseOf_cons, consBaseOf_cons, R.clPos_union_of_subset hT]

/-- **Property 2 (Materialization)**, incoherence: adding triples already in `cl_R(X)`
does not change whether `X` is incoherent. -/
theorem consBaseOf_inc_union {X T : Graph Iri Lit Bn} (hT : T ⊆ R.clPos X) :
    (R.consBaseOf D).inc (X ∪ T) ↔ (R.consBaseOf D).inc X := by
  rw [consBaseOf_inc, consBaseOf_inc, R.clPos_union_of_subset hT, R.inconsistent_union_iff hT]

end Regime

/-! ## Layer 2: ground entries -/

/-- A ground entry `⟨A, c; E⟩`: premises, a conclusion (`none` is `⊥`, an incompatibility
entry), and a set of ground defeaters.  A defeater pattern with variables of its own is
represented by all of its instances, so those variables are read existentially. -/
structure Entry (Iri Lit Bn : Type) where
  prem : Graph Iri Lit Bn
  concl : Option (Triple (Term Iri Lit Bn))
  defeaters : Set (Graph Iri Lit Bn)

/-- An entry applies at `K` when its premises are in `K` and no defeater is contained
in `K`. -/
def Entry.Applies (e : Entry Iri Lit Bn) (K : Graph Iri Lit Bn) : Prop :=
  e.prem ⊆ K ∧ ∀ D ∈ e.defeaters, ¬ D ⊆ K

/-- A set of ground entries over `V`, range-restricted and closed under renamings.

Uniformity is stated for a pair `ρ`, `ρ'` with `ρ'` undoing `ρ` on the terms of the
premises: the renamed entry has the renamed premises and conclusion, and each of its
defeaters is carried back by `ρ'` to a defeater of the original entry.  Guards of a pattern
entry (such as `X ≠ Y`) are absorbed into which ground entries belong to the set. -/
structure Entries (Iri Lit Bn : Type) (V : Set Iri) where
  entries : Set (Entry Iri Lit Bn)
  /-- (1) range restriction -/
  range : ∀ e ∈ entries, ∀ c, e.concl = some c →
    ∀ x ∈ c.terms, x ∈ e.prem.terms ∨ ∃ v ∈ V, x = Term.iri v
  /-- (2) uniformity under renamings -/
  uniform : ∀ (ρ ρ' : Term Iri Lit Bn → Term Iri Lit Bn), FixesLV V ρ → FixesLV V ρ' →
    ∀ e ∈ entries, (∀ t ∈ e.prem, ∀ x ∈ t.terms, ρ' (ρ x) = x) →
      ∃ e' ∈ entries, e'.prem = Graph.mapT ρ e.prem ∧
        e'.concl = e.concl.map (Triple.map ρ) ∧
        ∀ D' ∈ e'.defeaters, Graph.mapT ρ' D' ∈ e.defeaters

namespace Entries
variable (E : Entries Iri Lit Bn V)

/-- `D*` at `K`: the conclusions of the entries applying at `K`. -/
def dstar (K : Graph Iri Lit Bn) : Graph Iri Lit Bn :=
  {c | ∃ e ∈ E.entries, e.Applies K ∧ e.concl = some c}

/-- An incompatibility entry applies at `K`. -/
def Incompat (K : Graph Iri Lit Bn) : Prop :=
  ∃ e ∈ E.entries, e.Applies K ∧ e.concl = none

/-- Application is invariant under renamings: if `e` applies at `K` and `ρ` renames `K`,
the renamed entry applies at `ρ(K)`. -/
theorem applies_map {ρ : Term Iri Lit Bn → Term Iri Lit Bn} {K : Graph Iri Lit Bn}
    (h : Renames V ρ K) {e : Entry Iri Lit Bn} (he : e ∈ E.entries) (ha : e.Applies K) :
    ∃ e' ∈ E.entries, e'.Applies (Graph.mapT ρ K) ∧ e'.concl = e.concl.map (Triple.map ρ) := by
  obtain ⟨ρ', hρ', hinv⟩ := h.inv
  obtain ⟨e', he', hprem, hconcl, hdef⟩ :=
    E.uniform ρ ρ' h.fixes hρ' e he (fun t ht x hx => hinv t (ha.1 ht) x hx)
  refine ⟨e', he', ⟨?_, ?_⟩, hconcl⟩
  · rw [hprem]
    exact Graph.mapT_mono ρ ha.1
  · intro D' hD' hsub
    apply ha.2 _ (hdef D' hD')
    calc Graph.mapT ρ' D' ⊆ Graph.mapT ρ' (Graph.mapT ρ K) := Graph.mapT_mono ρ' hsub
      _ = K := by
          rw [Graph.mapT_mapT]
          exact Graph.mapT_eq_self K (fun t ht x hx => hinv t ht x hx)

/-- The round of defaults of a set of entries. -/
def step : DefaultStep Iri Lit Bn V where
  dstar := E.dstar
  incompat := E.Incompat
  terms_dstar K := by
    rintro x ⟨c, ⟨e, he, ha, hc⟩, hx⟩
    rcases E.range e he c hc x hx with ⟨a, ha', hxa⟩ | ⟨v, hv, hveq⟩
    · exact Or.inl ⟨a, ha.1 ha', hxa⟩
    · exact Or.inr ⟨v, hv, hveq.symm⟩
  dstar_map ρ K h := by
    rintro _ ⟨c, ⟨e, he, ha, hc⟩, rfl⟩
    obtain ⟨e', he', ha', hc'⟩ := E.applies_map h he ha
    exact ⟨e', he', ha', hc'.trans (congrArg (Option.map (Triple.map ρ)) hc)⟩
  incompat_map ρ K h := by
    rintro ⟨e, he, ha, hc⟩
    obtain ⟨e', he', ha', hc'⟩ := E.applies_map h he ha
    exact ⟨e', he', ha', hc'.trans (congrArg (Option.map (Triple.map ρ)) hc)⟩

end Entries

/-! ## Lemma A and the general theorem at the entries base -/

/-- **Lemma A.** A regime with a set of entries is a `ConsBase`: Containment, no new terms,
and invariance under renamings hold.  (Primeness is built into `ConsBase.base`.) -/
def Regime.entriesBase (R : Regime Iri Lit Bn V) (E : Entries Iri Lit Bn V) :
    ConsBase Iri Lit Bn V :=
  R.consBaseOf E.step

namespace Regime
variable (R : Regime Iri Lit Bn V) (E : Entries Iri Lit Bn V)
variable {N : Set (Term Iri Lit Bn)}

theorem entriesBase_cons (X : Graph Iri Lit Bn) :
    (R.entriesBase E).cons X = R.clPos (R.clPos X ∪ E.dstar (R.clPos X)) := rfl

theorem entriesBase_inc (X : Graph Iri Lit Bn) :
    (R.entriesBase E).inc X ↔ R.Inconsistent X ∨ E.Incompat (R.clPos X) := Iff.rfl

/-- **The general theorem at the entries base**, part (T). -/
theorem entries_general {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) (hN : N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    FitEnt ((R.entriesBase E).base N) (G.inst νsk) H ↔
      SimpleEntails (R.clPos (R.clPos G ∪ E.dstar (R.clPos G))) H :=
  (R.entriesBase E).general hA hN hS

/-- **The general theorem at the entries base**, part (P). -/
theorem entries_incoherent_iff {G H : Graph Iri Lit Bn} (hA : Admissible N G H V)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V G H νsk σ) :
    ((R.entriesBase E).base N).herbrand.Incoherent N (G.inst νsk) ↔
      R.Inconsistent G ∨ E.Incompat (R.clPos G) :=
  (R.entriesBase E).incoherent_iff_inc hA hS

/-- **Property 1 (Defeat witness).** If `X ⊆ Y` and a consequence of `X` is not a
consequence of `Y`, then some entry with a conclusion applies at `cl_R(X)` and has a
defeater contained in `cl_R(Y)` (and not in `cl_R(X)`). -/
theorem defeat_witness {X Y : Graph Iri Lit Bn} (hXY : X ⊆ Y)
    {t : Triple (Term Iri Lit Bn)} (hX : t ∈ (R.entriesBase E).cons X)
    (hY : t ∉ (R.entriesBase E).cons Y) :
    ∃ e ∈ E.entries, (∃ c, e.concl = some c) ∧ e.Applies (R.clPos X) ∧
      ∃ D ∈ e.defeaters, D ⊆ R.clPos Y ∧ ¬ D ⊆ R.clPos X := by
  by_contra hno
  apply hY
  have hK : R.clPos X ⊆ R.clPos Y := R.clPos_mono hXY
  have hd : E.dstar (R.clPos X) ⊆ E.dstar (R.clPos Y) := by
    rintro c ⟨e, he, ha, hc⟩
    refine ⟨e, he, ⟨Set.Subset.trans ha.1 hK, ?_⟩, hc⟩
    intro D hD hsub
    exact hno ⟨e, he, ⟨c, hc⟩, ha, D, hD, hsub, ha.2 D hD⟩
  rw [entriesBase_cons] at hX ⊢
  exact R.clPos_mono (Set.union_subset_union hK hd) hX

/-- **Property 1, counterpart for incoherence (Lost incoherence).** If `X ⊆ Y`, `X` is
incoherent and `Y` is not, then some incompatibility entry applies at `cl_R(X)` and has a
defeater contained in `cl_R(Y)` (and not in `cl_R(X)`).  `R`-inconsistency is monotone, so
the incoherence of `X` must come from an entry. -/
theorem incoherence_witness {X Y : Graph Iri Lit Bn} (hXY : X ⊆ Y)
    (hX : (R.entriesBase E).inc X) (hY : ¬ (R.entriesBase E).inc Y) :
    ∃ e ∈ E.entries, e.concl = none ∧ e.Applies (R.clPos X) ∧
      ∃ D ∈ e.defeaters, D ⊆ R.clPos Y ∧ ¬ D ⊆ R.clPos X := by
  rw [entriesBase_inc] at hX hY
  rcases hX with hi | ⟨e, he, ha, hc⟩
  · exact (hY (Or.inl (R.inconsistent_mono hXY hi))).elim
  · by_contra hno
    apply hY
    right
    refine ⟨e, he, ⟨Set.Subset.trans ha.1 (R.clPos_mono hXY), ?_⟩, hc⟩
    intro D hD hsub
    exact hno ⟨e, he, hc, ha, D, hD, hsub, ha.2 D hD⟩

end Regime

end ISRDF
