import ISRDF.Semantics

/-!
# Ontology-relative regimes

New declarations only; nothing earlier in the library is changed.

The corollary checked.  Let `R` be a regime over `V` and `O` a ground graph, the ontology.
Put `R_O = R ∪ {⟨∅, t⟩ | t ∈ O}`.  Then `R_O` is a regime over `V` together with the names of
`O`; `cl_{R_O}(X) = cl_R(X ∪ O)` for every `X`; and, by Theorem 2, implication in the models
fit for `B_{R_O}` holds from `G` to `H` iff `G ∪ O` is `R`-inconsistent or
`cl_R(G ∪ O) \ {⊥}` simply entails `H`.

One difference from the manuscript's statement.  The manuscript lets `V` contain literals,
so its ontology may contain literals.  The library's `V` is a set of IRIs (`Regime`,
Definition 4 in `Rdf.lean`), and its range restriction asks every term of a conclusion to
occur in the premises or to be an IRI in `V`.  A rule `⟨∅, t⟩` therefore needs every term
of `t` to be an IRI.  So the ontology here is a graph all of whose terms are IRIs
(`Graph.IriOnly`), which is ground and has no literal.

* `Regime.withOntology` is `R_O`, as a `Regime` over `V ∪ O.iris`.
* `Regime.cl_withOntology`, `Regime.clPos_withOntology` and
  `Regime.inconsistent_withOntology` are the closure equation.
* `Regime.ontology_relative` is the corollary, from `closure_regimes`.
* `Regime.ontology_relative_incoherent` is its counterpart for incoherence, from
  `incoherence_recovery`.
-/

set_option autoImplicit false

namespace ISRDF

variable {Iri Lit Bn : Type} {V : Set Iri}

/-- The IRIs occurring in a graph. -/
def Graph.iris (O : Graph Iri Lit Bn) : Set Iri := {i | Term.iri i ∈ O.terms}

/-- Every term occurring in the graph is an IRI.  Such a graph is ground and has no literal. -/
def Graph.IriOnly (O : Graph Iri Lit Bn) : Prop :=
  ∀ t ∈ O, ∀ x ∈ t.terms, ∃ i : Iri, x = Term.iri i

theorem Graph.mem_iris {O : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)} {i : Iri}
    (ht : t ∈ O) (hi : Term.iri i ∈ t.terms) : i ∈ O.iris :=
  ⟨t, ht, hi⟩

/-- A graph whose terms are all IRIs is ground. -/
theorem Graph.IriOnly.ground {O : Graph Iri Lit Bn} (hO : O.IriOnly) : O.Ground := by
  intro t ht x hx
  obtain ⟨i, rfl⟩ := hO t ht x hx
  trivial

namespace Regime
variable (R : Regime Iri Lit Bn V) (O : Graph Iri Lit Bn)

/-- The rules `⟨∅, t⟩`, one for each triple `t` of the ontology. -/
def ontRules : Set (Rule Iri Lit Bn) := {r | ∃ t ∈ O, r = ⟨∅, some t⟩}

/-- `R_O = R ∪ {⟨∅, t⟩ | t ∈ O}`, a regime over `V` and the IRIs of `O`. -/
def withOntology (hO : O.IriOnly) : Regime Iri Lit Bn (V ∪ O.iris) where
  rules := R.rules ∪ ontRules O
  range := by
    rintro r (hr | ⟨t, ht, rfl⟩) c hc x hx
    · rcases R.range r hr c hc x hx with h | ⟨v, hv, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, Or.inl hv, rfl⟩
    · have h : t = c := Option.some.inj hc
      subst h
      obtain ⟨i, rfl⟩ := hO t ht x hx
      exact Or.inr ⟨i, Or.inr (Graph.mem_iris ht hx), rfl⟩
  uniform := by
    rintro ρ ⟨hl, hv⟩ r (hr | ⟨t, ht, rfl⟩)
    · exact Or.inl (R.uniform ρ ⟨hl, fun v h => hv v (Or.inl h)⟩ r hr)
    · refine Or.inr ⟨t, ht, ?_⟩
      have hfix : ∀ x ∈ t.terms, ρ x = x := by
        intro x hx
        obtain ⟨i, rfl⟩ := hO t ht x hx
        exact hv i (Or.inr (Graph.mem_iris ht hx))
      have hs : ρ t.s = t.s := hfix t.s (by simp [Triple.terms])
      have hp : ρ t.p = t.p := hfix t.p (by simp [Triple.terms])
      have ho : ρ t.o = t.o := hfix t.o (by simp [Triple.terms])
      have ht' : Triple.map ρ t = t := by
        cases t
        simp_all [Triple.map]
      simp [Rule.map, Graph.mapT, ht']

/-- The closure under `R_O` of `X` is the closure under `R` of `X ∪ O`, at `⊥` as well. -/
theorem cl_withOntology (hO : O.IriOnly) (X : Graph Iri Lit Bn)
    (c : Option (Triple (Term Iri Lit Bn))) :
    Cl (R.withOntology O hO) X c ↔ Cl R (X ∪ O) c := by
  constructor
  · intro h
    induction h with
    | base ht => exact Cl.base (Or.inl ht)
    | step hr _ ih =>
      rcases hr with hr | ⟨t, ht, rfl⟩
      · exact Cl.step hr ih
      · exact Cl.base (Or.inr ht)
  · intro h
    induction h with
    | @base t ht =>
      rcases ht with ht | ht
      · exact Cl.base ht
      · have hr : (⟨∅, some t⟩ : Rule Iri Lit Bn) ∈ (R.withOntology O hO).rules :=
          Or.inr ⟨t, ht, rfl⟩
        exact Cl.step hr (fun a ha => False.elim ((Set.mem_empty_iff_false a).mp ha))
    | step hr _ ih => exact Cl.step (Or.inl hr) ih

/-- `cl_{R_O}(X) \ {⊥} = cl_R(X ∪ O) \ {⊥}`. -/
theorem clPos_withOntology (hO : O.IriOnly) (X : Graph Iri Lit Bn) :
    (R.withOntology O hO).clPos X = R.clPos (X ∪ O) :=
  Set.ext fun t => R.cl_withOntology O hO X (some t)

/-- `X` is `R_O`-inconsistent iff `X ∪ O` is `R`-inconsistent. -/
theorem inconsistent_withOntology (hO : O.IriOnly) (X : Graph Iri Lit Bn) :
    (R.withOntology O hO).Inconsistent X ↔ R.Inconsistent (X ∪ O) :=
  R.cl_withOntology O hO X none

variable {N : Set (Term Iri Lit Bn)}

/-- **Corollary (Ontology-relative regimes).**  Implication in the models fit for `B_{R_O}`
is `R`-entailment from the graph together with the ontology. -/
theorem ontology_relative (hO : O.IriOnly) {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H (V ∪ O.iris)) :
    FitEnt ((R.withOntology O hO).base N) G H ↔
      R.Inconsistent (G ∪ O) ∨ SimpleEntails (R.clPos (G ∪ O)) H := by
  refine (closure_regimes (R.withOntology O hO) hA).trans ?_
  show (R.withOntology O hO).Inconsistent G ∨
      SimpleEntails ((R.withOntology O hO).clPos G) H ↔ _
  rw [R.inconsistent_withOntology O hO, R.clPos_withOntology O hO]

/-- The counterpart for incoherence: `G` is incoherent in the Herbrand model of `B_{R_O}`
iff `G ∪ O` is `R`-inconsistent. -/
theorem ontology_relative_incoherent (hO : O.IriOnly) {G : Graph Iri Lit Bn}
    (hA : Admissible N G ∅ (V ∪ O.iris)) :
    ((R.withOntology O hO).base N).herbrand.Incoherent N G ↔ R.Inconsistent (G ∪ O) :=
  (incoherence_recovery (R.withOntology O hO) hA).trans (R.inconsistent_withOntology O hO G)

end Regime

end ISRDF
