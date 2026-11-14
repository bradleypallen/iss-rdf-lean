import ISRDF.Entries

/-!
# Implication-Space Semantics for RDF — Part 5: examples and counterexamples

Concrete entry sets over the empty regime, showing that the hypotheses of the general
theorem are inhabited by a nonmonotone base and that the structural failures are real.
Everything is parametric in `Iri Lit Bn` and in `V`: the predicates of the entries are
IRIs assumed to lie in `V`, and the named terms carry distinctness hypotheses.  The carrier
types are instantiated only in `E0_instance_nat`, which exhibits one closed instance.

* **Schemas.**  `Schema`, `schemaEntries`: all ground instances of a set of two-variable
  entries `X p Y |~ c unless d₁, …`, as an `Entries`.  This is the pattern-to-ground step
  for this fragment (one premise `X p Y`, defeaters without variables of their own, no
  guards).
* **Example 1.**  `E0`: all ground instances of `X p Y |~ X q X unless X p X`.
  `E0_nonmonotone` (1a) and `E0_def11_vs_skolem` (1b, Definition 11 against the Skolem
  reading), with `E0_admissible` and `E0_def11_vs_skolem_exists` showing that the
  hypotheses of 1b are satisfiable.
* **Example 3.**  `cautious_monotony_fails` (entry `X p Y |~ X q Y unless X q X`) and
  `cut_fails` (entries `X p Y |~ X q Y` and `X q Y |~ X r Y`), each also stated for the
  base relation (`cautious_monotony_fails_rel`, `cut_fails_rel`).
* **Example 2.**  `redundant_bnode_not_inert` (entry `X p Y |~ Y q Y unless Y p Y`): two
  graphs that simply entail each other have consequences that do not.
-/

set_option autoImplicit false

namespace ISRDF
namespace Examples

variable {Iri Lit Bn : Type} {V : Set Iri}

/-! ## Triples with an IRI predicate -/

/-- The triple `s p o` with an IRI in predicate position. -/
abbrev tri (s : Term Iri Lit Bn) (p : Iri) (o : Term Iri Lit Bn) : Triple (Term Iri Lit Bn) :=
  ⟨s, Term.iri p, o⟩

theorem tri_inj {s o s' o' : Term Iri Lit Bn} {p p' : Iri} :
    tri s p o = tri s' p' o' ↔ s = s' ∧ p = p' ∧ o = o' := by
  constructor
  · intro h
    exact ⟨congrArg Triple.s h, Term.iri.inj (congrArg Triple.p h), congrArg Triple.o h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem mem_terms_tri {s o x : Term Iri Lit Bn} {p : Iri} :
    x ∈ (tri s p o).terms ↔ x = s ∨ x = Term.iri p ∨ x = o := by
  simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem tri_mem_lex {N : Set (Term Iri Lit Bn)} {s o : Term Iri Lit Bn} {p : Iri}
    (hs : s ∈ N) (hp : Term.iri p ∈ N) (ho : o ∈ N) : tri s p o ∈ Lex N := by
  intro x hx
  rcases mem_terms_tri.1 hx with rfl | rfl | rfl
  · exact hs
  · exact hp
  · exact ho

theorem ground_singleton {s o : Term Iri Lit Bn} {p : Iri} (hs : s.IsName) (ho : o.IsName) :
    Graph.Ground ({tri s p o} : Graph Iri Lit Bn) := by
  intro t ht x hx
  rw [Set.mem_singleton_iff.1 ht] at hx
  rcases mem_terms_tri.1 hx with rfl | rfl | rfl
  · exact hs
  · trivial
  · exact ho

/-- For a single conclusion the base relation is membership in `Cons`. -/
theorem rel_singleton (C : ConsBase Iri Lit Bn V) (N : Set (Term Iri Lit Bn))
    {Γ : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)} :
    (C.base N).rel Γ {t} ↔ t ∈ C.cons Γ := by
  constructor
  · rintro (⟨u, hu, hc⟩ | ⟨he, -⟩)
    · rw [Set.mem_singleton_iff.1 hu] at hc
      exact hc
    · exact (Set.singleton_ne_empty _ he).elim
  · exact fun h => Or.inl ⟨t, Set.mem_singleton _, h⟩

/-! ## Two-variable schemas -/

/-- A position in a schema: the first variable, the second variable, or a constant IRI. -/
inductive Slot (Iri : Type)
  | fst
  | snd
  | const (v : Iri)

/-- The term at a slot under the assignment `X := x`, `Y := y`. -/
def Slot.eval (x y : Term Iri Lit Bn) (z : Slot Iri) : Term Iri Lit Bn :=
  match z with
  | Slot.fst => x
  | Slot.snd => y
  | Slot.const v => Term.iri v

/-- The constant of a slot, if any, lies in `V`. -/
def Slot.InV (V : Set Iri) (z : Slot Iri) : Prop :=
  match z with
  | Slot.const v => v ∈ V
  | _ => True

theorem Slot.eval_map {ρ : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (x y : Term Iri Lit Bn) {z : Slot Iri} (hz : z.InV V) :
    ρ (z.eval x y) = z.eval (ρ x) (ρ y) := by
  cases z with
  | fst => rfl
  | snd => rfl
  | const v => exact hρ.2 v hz

theorem map_eval {ρ : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (x y : Term Iri Lit Bn) {t : Triple (Slot Iri)} (ht : ∀ z ∈ t.terms, z.InV V) :
    Triple.map ρ (t.map (Slot.eval x y)) = t.map (Slot.eval (ρ x) (ρ y)) := by
  rw [Triple.map_map]
  exact Triple.map_congr (fun z hz => Slot.eval_map hρ x y (ht z hz))

theorem inV_terms {a b c : Slot Iri} (ha : a.InV V) (hb : b.InV V) (hc : c.InV V) :
    ∀ z ∈ (Triple.mk a b c).terms, z.InV V := by
  intro z hz
  simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- The entry schema `X p Y |~ concl unless d₁, …`: one premise `X p Y`, a conclusion and
single-triple defeaters over `X`, `Y` and constants. -/
structure Schema (Iri : Type) where
  p : Iri
  concl : Triple (Slot Iri)
  defeaters : Set (Triple (Slot Iri))

/-- The constants of a schema lie in `V`. -/
structure Schema.Over (V : Set Iri) (s : Schema Iri) : Prop where
  hp : s.p ∈ V
  hconcl : ∀ z ∈ s.concl.terms, z.InV V
  hdef : ∀ d ∈ s.defeaters, ∀ z ∈ d.terms, z.InV V

/-- The ground instance of a schema at `X := x`, `Y := y`. -/
def Schema.inst (s : Schema Iri) (x y : Term Iri Lit Bn) : Entry Iri Lit Bn where
  prem := {tri x s.p y}
  concl := some (s.concl.map (Slot.eval x y))
  defeaters := {D | ∃ d ∈ s.defeaters, D = {d.map (Slot.eval x y)}}

/-- All ground instances of a set of schemas over `V` form an `Entries`: they are
range-restricted and closed under renamings. -/
def schemaEntries (S : Set (Schema Iri)) (hS : ∀ s ∈ S, s.Over V) : Entries Iri Lit Bn V where
  entries := {e | ∃ s ∈ S, ∃ x y, e = s.inst x y}
  range := by
    rintro _ ⟨s, hs, x, y, rfl⟩ c hc t ht
    rw [← Option.some.inj hc] at ht
    obtain ⟨z, hz, rfl⟩ := (Triple.mem_terms_map _ _).1 ht
    cases z with
    | fst => exact Or.inl ⟨tri x s.p y, Set.mem_singleton _, mem_terms_tri.2 (Or.inl rfl)⟩
    | snd =>
      exact Or.inl ⟨tri x s.p y, Set.mem_singleton _, mem_terms_tri.2 (Or.inr (Or.inr rfl))⟩
    | const v => exact Or.inr ⟨v, (hS s hs).hconcl _ hz, rfl⟩
  uniform := by
    rintro ρ ρ' hρ hρ' _ ⟨s, hs, x, y, rfl⟩ hinv
    have hx : ρ' (ρ x) = x :=
      hinv (tri x s.p y) (Set.mem_singleton _) x (mem_terms_tri.2 (Or.inl rfl))
    have hy : ρ' (ρ y) = y :=
      hinv (tri x s.p y) (Set.mem_singleton _) y (mem_terms_tri.2 (Or.inr (Or.inr rfl)))
    refine ⟨s.inst (ρ x) (ρ y), ⟨s, hs, ρ x, ρ y, rfl⟩, ?_, ?_, ?_⟩
    · show ({tri (ρ x) s.p (ρ y)} : Graph Iri Lit Bn) = Graph.mapT ρ {tri x s.p y}
      rw [Graph.mapT, Set.image_singleton]
      show ({tri (ρ x) s.p (ρ y)} : Graph Iri Lit Bn) = {⟨ρ x, ρ (Term.iri s.p), ρ y⟩}
      rw [hρ.2 s.p (hS s hs).hp]
    · show some (s.concl.map (Slot.eval (ρ x) (ρ y))) =
        some (Triple.map ρ (s.concl.map (Slot.eval x y)))
      rw [map_eval hρ x y (hS s hs).hconcl]
    · rintro _ ⟨d, hd, rfl⟩
      refine ⟨d, hd, ?_⟩
      rw [Graph.mapT, Set.image_singleton, map_eval hρ' (ρ x) (ρ y) ((hS s hs).hdef d hd),
        hx, hy]

/-- The base of a set of schemas over the empty regime. -/
abbrev schemaBase (S : Set (Schema Iri)) (hS : ∀ s ∈ S, s.Over V) : ConsBase Iri Lit Bn V :=
  (emptyRegime Iri Lit Bn V).entriesBase (schemaEntries S hS)

/-- `Cons` for a set of schemas over the empty regime: `K` together with the conclusions of
the instances whose premise is in `K` and none of whose defeaters is. -/
theorem mem_cons_schema (S : Set (Schema Iri)) (hS : ∀ s ∈ S, s.Over V)
    {K : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)} :
    t ∈ (schemaBase S hS).cons K ↔
      t ∈ K ∨ ∃ s ∈ S, ∃ x y, tri x s.p y ∈ K ∧
        (∀ d ∈ s.defeaters, d.map (Slot.eval x y) ∉ K) ∧ s.concl.map (Slot.eval x y) = t := by
  rw [Regime.entriesBase_cons]
  simp only [emptyRegime_clPos]
  constructor
  · rintro (h | ⟨e, ⟨s, hs, x, y, rfl⟩, ha, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, x, y, ha.1 (Set.mem_singleton _),
        fun d hd hmem => ha.2 _ ⟨d, hd, rfl⟩ (Set.singleton_subset_iff.2 hmem),
        Option.some.inj hc⟩
  · rintro (h | ⟨s, hs, x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨s.inst x y, ⟨s, hs, x, y, rfl⟩,
        ⟨Set.singleton_subset_iff.2 hprem, ?_⟩, rfl⟩
      rintro _ ⟨d, hd, rfl⟩ hsub
      exact hdef d hd (Set.singleton_subset_iff.1 hsub)

variable {p q r : Iri}

/-! ## Example 1: `X p Y |~ X q X unless X p X` -/

/-- The schema `X p Y |~ X q X unless X p X`. -/
def s0 (p q : Iri) : Schema Iri :=
  ⟨p, ⟨Slot.fst, Slot.const q, Slot.fst⟩, {⟨Slot.fst, Slot.const p, Slot.fst⟩}⟩

theorem s0_over (hp : p ∈ V) (hq : q ∈ V) :
    ∀ s ∈ ({s0 p q} : Set (Schema Iri)), s.Over V := by
  intro s hs
  rw [Set.mem_singleton_iff.1 hs]
  refine ⟨hp, inV_terms trivial hq trivial, ?_⟩
  intro d hd
  rw [Set.mem_singleton_iff.1 hd]
  exact inV_terms trivial hp trivial

/-- **Example 1.** `E0`: all ground instances of `X p Y |~ X q X unless X p X`.  It is an
`Entries` (range restriction and uniformity hold). -/
abbrev E0 (hp : p ∈ V) (hq : q ∈ V) : Entries Iri Lit Bn V :=
  schemaEntries {s0 p q} (s0_over hp hq)

/-- The base of `E0` over the empty regime. -/
abbrev E0base (hp : p ∈ V) (hq : q ∈ V) : ConsBase Iri Lit Bn V :=
  (emptyRegime Iri Lit Bn V).entriesBase (E0 hp hq)

theorem mem_cons_E0 (hp : p ∈ V) (hq : q ∈ V) {K : Graph Iri Lit Bn}
    {t : Triple (Term Iri Lit Bn)} :
    t ∈ (E0base hp hq).cons K ↔
      t ∈ K ∨ ∃ x y, tri x p y ∈ K ∧ tri x p x ∉ K ∧ t = tri x q x := by
  rw [mem_cons_schema]
  constructor
  · rintro (h | ⟨s, hs, x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · rw [Set.mem_singleton_iff.1 hs] at hprem hdef ⊢
      exact Or.inr ⟨x, y, hprem, hdef _ (Set.mem_singleton _), rfl⟩
  · rintro (h | ⟨x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨s0 p q, Set.mem_singleton _, x, y, hprem, ?_, rfl⟩
      intro d hd
      rw [Set.mem_singleton_iff.1 hd]
      exact hdef

/-- **Example 1a (Nonmonotone).** `a q a` is a consequence of `{a p c}` and is not a
consequence of the larger `{a p c, a p a}`. -/
theorem E0_nonmonotone (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q) {a c : Term Iri Lit Bn}
    (hac : a ≠ c) :
    tri a q a ∈ (E0base hp hq).cons {tri a p c} ∧
      tri a q a ∉ (E0base hp hq).cons {tri a p c, tri a p a} := by
  constructor
  · refine (mem_cons_E0 hp hq).2 (Or.inr ⟨a, c, Set.mem_singleton _, ?_, rfl⟩)
    intro h
    exact hac (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.2
  · intro h
    rcases (mem_cons_E0 hp hq).1 h with h | ⟨x, y, -, hdef, hc⟩
    · rcases Set.mem_insert_iff.1 h with h | h
      · exact hpq (tri_inj.1 h).2.1.symm
      · exact hpq (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1.symm
    · rw [← (tri_inj.1 hc).1] at hdef
      exact hdef (Set.mem_insert_of_mem _ (Set.mem_singleton _))

section Def11
variable {N : Set (Term Iri Lit Bn)}

/-- Example 1b, the Skolem side: for `G = {a p _:b}` and `H = {a q a}`, implication from
the Skolemization of `G` to `H` holds in the fit models (by `Regime.entries_general`). -/
theorem E0_skolem_side (hp : p ∈ V) (hq : q ∈ V) {a : Term Iri Lit Bn} (ha : a.IsName)
    {b : Bn} (hA : Admissible N {tri a p (Term.bnode b)} {tri a q a} V) (hN : N.Nonempty)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V {tri a p (Term.bnode b)} {tri a q a} νsk σ) :
    FitEnt ((E0base hp hq).base N) (Graph.inst νsk {tri a p (Term.bnode b)}) {tri a q a} := by
  refine (Regime.entries_general _ _ hA hN hS).2 ⟨fun _ => a, ?_⟩
  rw [Graph.inst_of_ground _ _ (ground_singleton ha ha), Set.singleton_subset_iff]
  refine (mem_cons_E0 hp hq).2 (Or.inr ⟨a, Term.bnode b, Set.mem_singleton _, ?_, rfl⟩)
  intro h
  have hab : a = Term.bnode b := (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.2
  rw [hab] at ha
  exact ha

/-- Example 1b, the Definition 11 side: for the same `G` and `H`, implication from `G`
itself to `H` fails.  The witness is the instance `_:b := a` of `G`, namely `{a p a}`,
where the defeater is present. -/
theorem E0_def11_side_fails (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q) {a : Term Iri Lit Bn}
    (ha : a.IsName) {b : Bn} (haN : a ∈ N) (hpN : Term.iri p ∈ N) (hqN : Term.iri q ∈ N) :
    ¬ FitEnt ((E0base hp hq).base N) {tri a p (Term.bnode b)} {tri a q a} := by
  intro h
  have hH := h _ ((E0base hp hq).base N).herbrand_fit
  rw [Model.gEnt_iff] at hH
  simp only [Base.herbrand_brG] at hH
  have hHinst : ∀ μ : Bn → Term Iri Lit Bn,
      Graph.inst μ ({tri a q a} : Graph Iri Lit Bn) = {tri a q a} :=
    fun μ => Graph.inst_of_ground _ μ (ground_singleton ha ha)
  have hνa : (fun _ : Bn => a) ∈ IMap N ({tri a p (Term.bnode b)} : Graph Iri Lit Bn) :=
    fun _ _ => haN
  have hμa : (fun _ : Bn => a) ∈ IMap N ({tri a q a} : Graph Iri Lit Bn) := fun _ _ => haN
  have hpair := hH {fun _ => a} (Set.singleton_subset_iff.2 hνa) (Set.singleton_nonempty _)
    (fun _ => {tri a q a}) (fun μ _ => ⟨Set.singleton_nonempty _, (hHinst μ).symm.subset⟩)
  rw [Set.biUnion_singleton] at hpair
  have hΓ : Graph.inst (fun _ : Bn => a) ({tri a p (Term.bnode b)} : Graph Iri Lit Bn) =
      {tri a p a} := by
    rw [Graph.inst, Graph.mapT, Set.image_singleton]
    show ({tri (Term.subst (fun _ : Bn => a) a) p a} : Graph Iri Lit Bn) = {tri a p a}
    rw [Term.subst_of_isName _ ha]
  rw [hΓ] at hpair
  have hΔlex : (⋃ μ ∈ IMap N ({tri a q a} : Graph Iri Lit Bn),
      ({tri a q a} : Graph Iri Lit Bn)) ⊆ Lex N := by
    intro t ht
    simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨-, -, ht⟩ := ht
    rw [Set.mem_singleton_iff.1 ht]
    exact tri_mem_lex haN hqN haN
  rcases (ConsBase.mem_frame_iff _
      (Set.singleton_subset_iff.2 (tri_mem_lex haN hpN haN)) hΔlex).1 hpair with
    ⟨t, ht, htc⟩ | ⟨hempty, -⟩
  · simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨-, -, ht⟩ := ht
    rw [Set.mem_singleton_iff.1 ht] at htc
    rcases (mem_cons_E0 hp hq).1 htc with h1 | ⟨x, y, -, hdef, hc⟩
    · exact hpq (tri_inj.1 (Set.mem_singleton_iff.1 h1)).2.1.symm
    · rw [← (tri_inj.1 hc).1] at hdef
      exact hdef (Set.mem_singleton _)
  · have hmem : tri a q a ∈ ⋃ μ ∈ IMap N ({tri a q a} : Graph Iri Lit Bn),
        ({tri a q a} : Graph Iri Lit Bn) := Set.mem_biUnion hμa (Set.mem_singleton _)
    rw [hempty] at hmem
    exact Set.notMem_empty _ hmem

/-- **Example 1b (Definition 11 against the Skolem reading).** For `G = {a p _:b}` and
`H = {a q a}`: reading `G` through its Skolemization grants `H`; reading `G` by
Definition 11 denies it. -/
theorem E0_def11_vs_skolem (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q) {a : Term Iri Lit Bn}
    (ha : a.IsName) {b : Bn} (hA : Admissible N {tri a p (Term.bnode b)} {tri a q a} V)
    {νsk : Bn → Term Iri Lit Bn} {σ : Term Iri Lit Bn → Term Iri Lit Bn}
    (hS : SkolemPair N V {tri a p (Term.bnode b)} {tri a q a} νsk σ) :
    FitEnt ((E0base hp hq).base N) (Graph.inst νsk {tri a p (Term.bnode b)}) {tri a q a} ∧
      ¬ FitEnt ((E0base hp hq).base N) {tri a p (Term.bnode b)} {tri a q a} := by
  have haN : a ∈ N :=
    hA.hH ⟨ha, tri a q a, Set.mem_singleton _, mem_terms_tri.2 (Or.inl rfl)⟩
  exact ⟨E0_skolem_side hp hq ha hA ⟨a, haN⟩ hS,
    E0_def11_side_fails hp hq hpq ha haN (hA.hV p hp) (hA.hV q hq)⟩

end Def11

/-- The hypotheses of Example 1b are satisfiable: given one more IRI `s` outside `V` and
different from `a`, the set `{a} ∪ V ∪ {s}` is admissible for `G = {a p _:b}` and
`H = {a q a}`. -/
theorem E0_admissible (hp : p ∈ V) (hq : q ∈ V) {a : Term Iri Lit Bn} (ha : a.IsName)
    (b : Bn) {s : Iri} (hs : s ∉ V) (has : a ≠ Term.iri s) :
    Admissible ({a} ∪ ((fun v => Term.iri v) '' V) ∪ {Term.iri s})
      ({tri a p (Term.bnode b)} : Graph Iri Lit Bn) {tri a q a} V where
  names := by
    rintro x ((hx | ⟨v, -, rfl⟩) | hx)
    · rw [Set.mem_singleton_iff.1 hx]
      exact ha
    · trivial
    · rw [Set.mem_singleton_iff.1 hx]
      trivial
  hG := by
    rintro x ⟨hx, t, ht, hxt⟩
    rw [Set.mem_singleton_iff.1 ht] at hxt
    rcases mem_terms_tri.1 hxt with rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
    · exact False.elim hx
  hH := by
    rintro x ⟨-, t, ht, hxt⟩
    rw [Set.mem_singleton_iff.1 ht] at hxt
    rcases mem_terms_tri.1 hxt with rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ⟨q, hq, rfl⟩)
    · exact Or.inl (Or.inl rfl)
  hV := fun v hv => Or.inl (Or.inr ⟨v, hv, rfl⟩)
  skolem := by
    have hbn : ∀ b' ∈ Graph.bnodes ({tri a p (Term.bnode b)} : Graph Iri Lit Bn), b' = b := by
      rintro b' ⟨t, ht, hb'⟩
      rw [Set.mem_singleton_iff.1 ht] at hb'
      rcases mem_terms_tri.1 hb' with h | h | h
      · rw [← h] at ha
        exact False.elim ha
      · cases h
      · exact Term.bnode.inj h
    refine ⟨fun _ => s, fun b₁ h₁ b₂ h₂ _ => (hbn b₁ h₁).trans (hbn b₂ h₂).symm,
      fun b' _ => ⟨Or.inr rfl, ?_⟩⟩
    rintro ((⟨-, t, ht, hx⟩ | ⟨-, t, ht, hx⟩) | ⟨v, hv, hveq⟩)
    · rw [Set.mem_singleton_iff.1 ht] at hx
      rcases mem_terms_tri.1 hx with h | h | h
      · exact has h.symm
      · have e : s = p := Term.iri.inj h
        exact hs (by rw [e]; exact hp)
      · cases h
    · rw [Set.mem_singleton_iff.1 ht] at hx
      rcases mem_terms_tri.1 hx with h | h | h
      · exact has h.symm
      · have e : s = q := Term.iri.inj h
        exact hs (by rw [e]; exact hq)
      · exact has h.symm
    · have e : v = s := Term.iri.inj hveq
      exact hs (by rw [← e]; exact hv)

/-- Example 1b with its hypotheses discharged: there are an admissible `N` and a
Skolemization for which the two readings come apart. -/
theorem E0_def11_vs_skolem_exists (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    {a : Term Iri Lit Bn} (ha : a.IsName) (b : Bn) {s : Iri} (hs : s ∉ V)
    (has : a ≠ Term.iri s) :
    ∃ (N : Set (Term Iri Lit Bn)) (νsk : Bn → Term Iri Lit Bn),
      FitEnt ((E0base hp hq).base N) (Graph.inst νsk {tri a p (Term.bnode b)}) {tri a q a} ∧
        ¬ FitEnt ((E0base hp hq).base N) {tri a p (Term.bnode b)} {tri a q a} := by
  have hA := E0_admissible hp hq ha b hs has
  obtain ⟨νsk, σ, hS⟩ := exists_skolemPair hA
  exact ⟨_, νsk, E0_def11_vs_skolem hp hq hpq ha hA hS⟩

/-- A closed instance (`Iri := ℕ`, `Lit := Empty`, `Bn := Unit`, `V := {0, 1}`): the
hypotheses of the general theorem are inhabited by a base on which Definition 11 in
antecedent position and the Skolem reading disagree. -/
theorem E0_instance_nat :
    ∃ (V : Set ℕ) (C : ConsBase ℕ Empty Unit V) (N : Set (Term ℕ Empty Unit))
      (νsk : Unit → Term ℕ Empty Unit) (G H : Graph ℕ Empty Unit),
      FitEnt (C.base N) (G.inst νsk) H ∧ ¬ FitEnt (C.base N) G H := by
  have hp : (0 : ℕ) ∈ ({0, 1} : Set ℕ) := by simp
  have hq : (1 : ℕ) ∈ ({0, 1} : Set ℕ) := by simp
  obtain ⟨N, νsk, h⟩ := E0_def11_vs_skolem_exists (Lit := Empty) (Bn := Unit) hp hq
    (by decide) (a := Term.iri 3) trivial () (s := 2) (by simp) (by simp)
  exact ⟨_, _, N, νsk, _, _, h⟩

/-! ## Example 3: Cautious Monotony and Cut fail at default conclusions -/

/-- The schema `X p Y |~ X q Y unless X q X`. -/
def sCM (p q : Iri) : Schema Iri :=
  ⟨p, ⟨Slot.fst, Slot.const q, Slot.snd⟩, {⟨Slot.fst, Slot.const q, Slot.fst⟩}⟩

theorem sCM_over (hp : p ∈ V) (hq : q ∈ V) :
    ∀ s ∈ ({sCM p q} : Set (Schema Iri)), s.Over V := by
  intro s hs
  rw [Set.mem_singleton_iff.1 hs]
  refine ⟨hp, inV_terms trivial hq trivial, ?_⟩
  intro d hd
  rw [Set.mem_singleton_iff.1 hd]
  exact inV_terms trivial hq trivial

/-- The base of `X p Y |~ X q Y unless X q X` over the empty regime. -/
abbrev CMbase (hp : p ∈ V) (hq : q ∈ V) : ConsBase Iri Lit Bn V :=
  schemaBase {sCM p q} (sCM_over hp hq)

theorem mem_cons_CM (hp : p ∈ V) (hq : q ∈ V) {K : Graph Iri Lit Bn}
    {t : Triple (Term Iri Lit Bn)} :
    t ∈ (CMbase hp hq).cons K ↔
      t ∈ K ∨ ∃ x y, tri x p y ∈ K ∧ tri x q x ∉ K ∧ t = tri x q y := by
  rw [mem_cons_schema]
  constructor
  · rintro (h | ⟨s, hs, x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · rw [Set.mem_singleton_iff.1 hs] at hprem hdef ⊢
      exact Or.inr ⟨x, y, hprem, hdef _ (Set.mem_singleton _), rfl⟩
  · rintro (h | ⟨x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨sCM p q, Set.mem_singleton _, x, y, hprem, ?_, rfl⟩
      intro d hd
      rw [Set.mem_singleton_iff.1 hd]
      exact hdef

/-- **Example 3 (Cautious Monotony fails).** With the entry `X p Y |~ X q Y unless X q X`
and `Γ = {a p a, a p c}`: `a q a` and `a q c` are both consequences of `Γ`, and `a q c` is
not a consequence of `Γ ∪ {a q a}`.  The added `a q a` is a default conclusion. -/
theorem cautious_monotony_fails (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    {a c : Term Iri Lit Bn} (hac : a ≠ c) :
    tri a q a ∈ (CMbase hp hq).cons {tri a p a, tri a p c} ∧
      tri a q c ∈ (CMbase hp hq).cons {tri a p a, tri a p c} ∧
      tri a q c ∉ (CMbase hp hq).cons ({tri a p a, tri a p c} ∪ {tri a q a}) := by
  have hnot : tri a q a ∉ ({tri a p a, tri a p c} : Graph Iri Lit Bn) := by
    intro h
    rcases Set.mem_insert_iff.1 h with h | h
    · exact hpq (tri_inj.1 h).2.1.symm
    · exact hpq (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1.symm
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_cons_CM hp hq).2 (Or.inr ⟨a, a, Set.mem_insert _ _, hnot, rfl⟩)
  · exact (mem_cons_CM hp hq).2
      (Or.inr ⟨a, c, Set.mem_insert_of_mem _ (Set.mem_singleton _), hnot, rfl⟩)
  · intro h
    rcases (mem_cons_CM hp hq).1 h with h | ⟨x, y, -, hdef, hc⟩
    · rcases h with h | h
      · rcases Set.mem_insert_iff.1 h with h | h
        · exact hpq (tri_inj.1 h).2.1.symm
        · exact hpq (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1.symm
      · exact hac (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.2.symm
    · rw [← (tri_inj.1 hc).1] at hdef
      exact hdef (Or.inr (Set.mem_singleton _))

/-- Example 3 (Cautious Monotony fails), for the base relation: `Γ |~ A` and `Γ |~ B`,
but not `Γ, A |~ B`. -/
theorem cautious_monotony_fails_rel (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    {a c : Term Iri Lit Bn} (hac : a ≠ c) (N : Set (Term Iri Lit Bn)) :
    ((CMbase hp hq).base N).rel {tri a p a, tri a p c} {tri a q a} ∧
      ((CMbase hp hq).base N).rel {tri a p a, tri a p c} {tri a q c} ∧
      ¬ ((CMbase hp hq).base N).rel ({tri a p a, tri a p c} ∪ {tri a q a}) {tri a q c} := by
  rw [rel_singleton, rel_singleton, rel_singleton]
  exact cautious_monotony_fails hp hq hpq hac

/-- The schema `X p Y |~ X q Y`, with no defeaters. -/
def sChain (p q : Iri) : Schema Iri := ⟨p, ⟨Slot.fst, Slot.const q, Slot.snd⟩, ∅⟩

theorem sCut_over (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V) :
    ∀ s ∈ ({sChain p q, sChain q r} : Set (Schema Iri)), s.Over V := by
  intro s hs
  rcases Set.mem_insert_iff.1 hs with hs | hs
  · rw [hs]
    exact ⟨hp, inV_terms trivial hq trivial, fun d hd => (Set.notMem_empty _ hd).elim⟩
  · rw [Set.mem_singleton_iff.1 hs]
    exact ⟨hq, inV_terms trivial hr trivial, fun d hd => (Set.notMem_empty _ hd).elim⟩

/-- The base of `X p Y |~ X q Y` and `X q Y |~ X r Y` over the empty regime. -/
abbrev CutBase (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V) : ConsBase Iri Lit Bn V :=
  schemaBase {sChain p q, sChain q r} (sCut_over hp hq hr)

theorem mem_cons_Cut (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V) {K : Graph Iri Lit Bn}
    {t : Triple (Term Iri Lit Bn)} :
    t ∈ (CutBase hp hq hr).cons K ↔
      t ∈ K ∨ (∃ x y, tri x p y ∈ K ∧ t = tri x q y) ∨
        (∃ x y, tri x q y ∈ K ∧ t = tri x r y) := by
  rw [mem_cons_schema]
  constructor
  · rintro (h | ⟨s, hs, x, y, hprem, -, rfl⟩)
    · exact Or.inl h
    · rcases Set.mem_insert_iff.1 hs with hs | hs
      · rw [hs] at hprem ⊢
        exact Or.inr (Or.inl ⟨x, y, hprem, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hs] at hprem ⊢
        exact Or.inr (Or.inr ⟨x, y, hprem, rfl⟩)
  · rintro (h | ⟨x, y, hprem, rfl⟩ | ⟨x, y, hprem, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨sChain p q, Set.mem_insert _ _, x, y, hprem,
        fun d hd => (Set.notMem_empty _ hd).elim, rfl⟩
    · exact Or.inr ⟨sChain q r, Set.mem_insert_of_mem _ (Set.mem_singleton _), x, y, hprem,
        fun d hd => (Set.notMem_empty _ hd).elim, rfl⟩

/-- **Example 3 (Cut fails).** With the entries `X p Y |~ X q Y` and `X q Y |~ X r Y` and
`Γ = {a p c}`: `a q c` is a consequence of `Γ`, `a r c` is a consequence of `Γ ∪ {a q c}`,
and `a r c` is not a consequence of `Γ`.  No defeater is involved: defaults are drawn in
one round and do not see each other's conclusions. -/
theorem cut_fails (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V) (hpq : p ≠ q) (hqr : q ≠ r)
    (hpr : p ≠ r) (a c : Term Iri Lit Bn) :
    tri a q c ∈ (CutBase hp hq hr).cons {tri a p c} ∧
      tri a r c ∈ (CutBase hp hq hr).cons ({tri a p c} ∪ {tri a q c}) ∧
      tri a r c ∉ (CutBase hp hq hr).cons {tri a p c} := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_cons_Cut hp hq hr).2 (Or.inr (Or.inl ⟨a, c, Set.mem_singleton _, rfl⟩))
  · exact (mem_cons_Cut hp hq hr).2
      (Or.inr (Or.inr ⟨a, c, Or.inr (Set.mem_singleton _), rfl⟩))
  · intro h
    rcases (mem_cons_Cut hp hq hr).1 h with h | ⟨x, y, -, hc⟩ | ⟨x, y, hprem, -⟩
    · exact hpr (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1.symm
    · exact hqr (tri_inj.1 hc).2.1.symm
    · exact hpq (tri_inj.1 (Set.mem_singleton_iff.1 hprem)).2.1.symm

/-- Example 3 (Cut fails), for the base relation: `Γ |~ A` and `Γ, A |~ B`, but not
`Γ |~ B`. -/
theorem cut_fails_rel (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V) (hpq : p ≠ q) (hqr : q ≠ r)
    (hpr : p ≠ r) (a c : Term Iri Lit Bn) (N : Set (Term Iri Lit Bn)) :
    ((CutBase hp hq hr).base N).rel {tri a p c} {tri a q c} ∧
      ((CutBase hp hq hr).base N).rel ({tri a p c} ∪ {tri a q c}) {tri a r c} ∧
      ¬ ((CutBase hp hq hr).base N).rel {tri a p c} {tri a r c} := by
  rw [rel_singleton, rel_singleton, rel_singleton]
  exact cut_fails hp hq hr hpq hqr hpr a c

/-! ## Example 2: redundant blank-node triples are not inert -/

/-- The schema `X p Y |~ Y q Y unless Y p Y`. -/
def sInert (p q : Iri) : Schema Iri :=
  ⟨p, ⟨Slot.snd, Slot.const q, Slot.snd⟩, {⟨Slot.snd, Slot.const p, Slot.snd⟩}⟩

theorem sInert_over (hp : p ∈ V) (hq : q ∈ V) :
    ∀ s ∈ ({sInert p q} : Set (Schema Iri)), s.Over V := by
  intro s hs
  rw [Set.mem_singleton_iff.1 hs]
  refine ⟨hp, inV_terms trivial hq trivial, ?_⟩
  intro d hd
  rw [Set.mem_singleton_iff.1 hd]
  exact inV_terms trivial hp trivial

/-- The base of `X p Y |~ Y q Y unless Y p Y` over the empty regime. -/
abbrev InertBase (hp : p ∈ V) (hq : q ∈ V) : ConsBase Iri Lit Bn V :=
  schemaBase {sInert p q} (sInert_over hp hq)

theorem mem_cons_Inert (hp : p ∈ V) (hq : q ∈ V) {K : Graph Iri Lit Bn}
    {t : Triple (Term Iri Lit Bn)} :
    t ∈ (InertBase hp hq).cons K ↔
      t ∈ K ∨ ∃ x y, tri x p y ∈ K ∧ tri y p y ∉ K ∧ t = tri y q y := by
  rw [mem_cons_schema]
  constructor
  · rintro (h | ⟨s, hs, x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · rw [Set.mem_singleton_iff.1 hs] at hprem hdef ⊢
      exact Or.inr ⟨x, y, hprem, hdef _ (Set.mem_singleton _), rfl⟩
  · rintro (h | ⟨x, y, hprem, hdef, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨sInert p q, Set.mem_singleton _, x, y, hprem, ?_, rfl⟩
      intro d hd
      rw [Set.mem_singleton_iff.1 hd]
      exact hdef

/-- **Example 2 (Redundant blank-node triples are not inert).** With the entry
`X p Y |~ Y q Y unless Y p Y`: the graphs `G1 = {a p a}` and `G2 = {a p a, a p _:b}`
simply entail each other, yet `Cons(G2)` simply entails `{_:b' q _:b'}` and `Cons(G1)` does
not.  The triple `a p _:b` is redundant for simple entailment and still triggers a default,
because `_:b` is read as a constant and `_:b p _:b` is absent. -/
theorem redundant_bnode_not_inert (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    {a : Term Iri Lit Bn} (ha : a.IsName) (b b' : Bn) :
    SimpleEntails ({tri a p a} : Graph Iri Lit Bn) {tri a p a, tri a p (Term.bnode b)} ∧
      SimpleEntails ({tri a p a, tri a p (Term.bnode b)} : Graph Iri Lit Bn) {tri a p a} ∧
      SimpleEntails ((InertBase hp hq).cons {tri a p a, tri a p (Term.bnode b)})
        {tri (Term.bnode b') q (Term.bnode b')} ∧
      ¬ SimpleEntails ((InertBase hp hq).cons {tri a p a})
        {tri (Term.bnode b') q (Term.bnode b')} := by
  have hsa : Term.subst (fun _ : Bn => a) a = a := Term.subst_of_isName _ ha
  have hba : Term.bnode b ≠ a := by
    intro h
    rw [← h] at ha
    exact ha
  refine ⟨⟨fun _ => a, ?_⟩, ⟨fun _ => a, ?_⟩, ⟨fun _ => Term.bnode b, ?_⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rcases Set.mem_insert_iff.1 ht with ht | ht
    · rw [ht]
      show tri (Term.subst (fun _ : Bn => a) a) p (Term.subst (fun _ : Bn => a) a) ∈
        ({tri a p a} : Graph Iri Lit Bn)
      rw [hsa]
      exact Set.mem_singleton _
    · rw [Set.mem_singleton_iff.1 ht]
      show tri (Term.subst (fun _ : Bn => a) a) p a ∈ ({tri a p a} : Graph Iri Lit Bn)
      rw [hsa]
      exact Set.mem_singleton _
  · rw [Graph.inst_of_ground _ _ (ground_singleton ha ha)]
    exact Set.singleton_subset_iff.2 (Set.mem_insert _ _)
  · rintro _ ⟨t, ht, rfl⟩
    rw [Set.mem_singleton_iff.1 ht]
    refine (mem_cons_Inert hp hq).2 (Or.inr ⟨a, Term.bnode b,
      Set.mem_insert_of_mem _ (Set.mem_singleton _), ?_, rfl⟩)
    intro h
    rcases Set.mem_insert_iff.1 h with h | h
    · exact hba (tri_inj.1 h).1
    · exact hba (tri_inj.1 (Set.mem_singleton_iff.1 h)).1
  · rintro ⟨μ, hμ⟩
    have h : tri (μ b') q (μ b') ∈ (InertBase hp hq).cons {tri a p a} :=
      hμ ⟨tri (Term.bnode b') q (Term.bnode b'), Set.mem_singleton _, rfl⟩
    rcases (mem_cons_Inert hp hq).1 h with h | ⟨x, y, hprem, hdef, -⟩
    · exact hpq (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1.symm
    · rw [(tri_inj.1 (Set.mem_singleton_iff.1 hprem)).2.2] at hdef
      exact hdef (Set.mem_singleton _)

end Examples
end ISRDF
