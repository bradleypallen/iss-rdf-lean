import ISRDF.Examples

/-!
# Implication-Space Semantics for RDF — Part 6: pattern entries and pattern rules

`Entries` (Part 4) is a set of *ground* entries closed under renamings.  This file gives the
pattern presentation and proves that the ground instances of well-formed pattern entries
form an `Entries`, and that the ground instances of well-formed pattern rules form a
`Regime`.

A pattern term (`PTerm`) is a variable, an IRI constant or a literal constant.  A pattern
entry (`PEntry`) has

* premises: a set of triple patterns;
* a conclusion: an optional triple pattern (`none` is an incompatibility entry);
* defeaters: a set of sets of triple patterns, which may use variables that do not occur in
  the premises;
* a guard: a predicate on substitutions.

Its ground instances (`PEntry.inst`) are one ground entry per substitution `θ` satisfying
the guard; the defeaters of that entry are all instances `D·η` for `η` agreeing with `θ` on
the premise variables, so defeater-only variables are read existentially.  Substitutions
range over all terms.

Well-formedness (`PEntry.WF`), the conditions under which `patternEntries` is an `Entries`:

1. every IRI constant in the premises is in `V`;
2. every term of the conclusion occurs in the premises or is an IRI constant in `V`;
3. every IRI constant in a defeater is in `V`;
4. the projection of the guard onto the premise variables (`projGuard`: "some substitution
   with these premise bindings satisfies the guard") is invariant (`GuardInvariant`):
   preserved by any `ρ` fixing `L ∪ V` that is undone, on the values of the premise
   variables, by another map fixing `L ∪ V`.

Variables in defeaters are unrestricted, and literal constants are allowed in premises and
defeaters.  The guard is not required to depend only on the premise variables; when it
does, condition 4 is invariance of the guard itself, and in general invariance of the guard
implies condition 4 (`GuardInvariant.proj`).

Invariant guards include `True`, conjunctions and disjunctions, comparisons between literal
values (`litGuard`, for any variables), anything depending only on which literals the
premise variables are bound to (`guardInvariant_litView`), and `X ≠ Y` or `X ≠ k` for
premise variables (`neGuard`, `neConstGuard`).
A guard that tests for a blank node is not invariant (`not_guardInvariant_isBnode`).

The section `Shapes` instantiates the layer at the shapes of the Wikidata case study.
-/

set_option autoImplicit false

namespace ISRDF

open Examples (tri tri_inj)

variable {Var Iri Lit Bn : Type} {V : Set Iri}

/-! ## Pattern terms and pattern graphs -/

/-- A pattern term: a variable, an IRI constant or a literal constant. -/
inductive PTerm (Var Iri Lit : Type)
  | var (x : Var)
  | iri (v : Iri)
  | lit (l : Lit)

/-- The term denoted by a pattern term under a substitution. -/
def PTerm.eval (θ : Var → Term Iri Lit Bn) (z : PTerm Var Iri Lit) : Term Iri Lit Bn :=
  match z with
  | PTerm.var x => θ x
  | PTerm.iri v => Term.iri v
  | PTerm.lit l => Term.lit l

/-- The constant of a pattern term, if it is an IRI, lies in `V`. -/
def PTerm.Const (V : Set Iri) (z : PTerm Var Iri Lit) : Prop :=
  match z with
  | PTerm.iri v => v ∈ V
  | _ => True

theorem PTerm.eval_map {ρ : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (θ : Var → Term Iri Lit Bn) {z : PTerm Var Iri Lit} (hz : z.Const V) :
    ρ (z.eval θ) = z.eval (fun x => ρ (θ x)) := by
  cases z with
  | var x => rfl
  | iri v => exact hρ.2 v hz
  | lit l => exact hρ.1 l

/-- A triple pattern. -/
abbrev PTriple (Var Iri Lit : Type) := Triple (PTerm Var Iri Lit)

/-- A set of triple patterns. -/
abbrev PGraph (Var Iri Lit : Type) := Set (PTriple Var Iri Lit)

theorem map_eval_triple {ρ : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (θ : Var → Term Iri Lit Bn) {t : PTriple Var Iri Lit} (ht : ∀ z ∈ t.terms, z.Const V) :
    Triple.map ρ (t.map (PTerm.eval θ)) = t.map (PTerm.eval (fun x => ρ (θ x))) := by
  rw [Triple.map_map]
  exact Triple.map_congr (fun z hz => PTerm.eval_map hρ θ (ht z hz))

namespace PGraph

/-- The instance of a set of triple patterns under a substitution. -/
def inst (θ : Var → Term Iri Lit Bn) (A : PGraph Var Iri Lit) : Graph Iri Lit Bn :=
  Triple.map (PTerm.eval θ) '' A

/-- The variables occurring in a set of triple patterns. -/
def vars (A : PGraph Var Iri Lit) : Set Var := {x | ∃ t ∈ A, PTerm.var x ∈ t.terms}

/-- Every IRI constant of `A` is in `V`. -/
def Over (V : Set Iri) (A : PGraph Var Iri Lit) : Prop := ∀ t ∈ A, ∀ z ∈ t.terms, z.Const V

/-- A map fixing `L ∪ V` commutes with instantiation of patterns over `V`. -/
theorem mapT_inst {ρ : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (θ : Var → Term Iri Lit Bn) {A : PGraph Var Iri Lit} (hA : A.Over V) :
    Graph.mapT ρ (A.inst θ) = A.inst (fun x => ρ (θ x)) := by
  show Triple.map ρ '' (Triple.map (PTerm.eval θ) '' A) =
    Triple.map (PTerm.eval (fun x => ρ (θ x))) '' A
  rw [Set.image_image]
  exact Set.image_congr (fun t ht => map_eval_triple hρ θ (hA t ht))

theorem eval_mem_terms_inst {A : PGraph Var Iri Lit} (θ : Var → Term Iri Lit Bn) {x : Var}
    (hx : x ∈ A.vars) : θ x ∈ (A.inst θ).terms := by
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t.map (PTerm.eval θ), ⟨t, ht, rfl⟩,
    (Triple.mem_terms_map _ _).2 ⟨PTerm.var x, hxt, rfl⟩⟩

/-- Instantiation depends only on the values of the variables that occur. -/
theorem inst_congr {A : PGraph Var Iri Lit} {θ θ' : Var → Term Iri Lit Bn}
    (h : ∀ x ∈ A.vars, θ x = θ' x) : A.inst θ = A.inst θ' := by
  refine Set.image_congr (fun t ht => Triple.map_congr (fun z hz => ?_))
  cases z with
  | var x => exact h x ⟨t, ht, hz⟩
  | iri v => rfl
  | lit l => rfl

theorem const_terms {a b c : PTerm Var Iri Lit} (ha : a.Const V) (hb : b.Const V)
    (hc : c.Const V) : ∀ z ∈ (Triple.mk a b c).terms, z.Const V := by
  intro z hz
  simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem over_empty : (∅ : PGraph Var Iri Lit).Over V :=
  fun _ ht => (Set.notMem_empty _ ht).elim

theorem over_singleton {t : PTriple Var Iri Lit} (ht : ∀ z ∈ t.terms, z.Const V) :
    ({t} : PGraph Var Iri Lit).Over V := by
  intro t' ht'
  rw [Set.mem_singleton_iff.1 ht']
  exact ht

theorem over_insert {t : PTriple Var Iri Lit} {A : PGraph Var Iri Lit}
    (ht : ∀ z ∈ t.terms, z.Const V) (hA : A.Over V) : (insert t A).Over V := by
  intro t' ht'
  rcases Set.mem_insert_iff.1 ht' with h | h
  · rw [h]
    exact ht
  · exact hA t' h

end PGraph

/-- The condition on a conclusion (shared by entries and rules): each of its terms occurs
in the premises or is an IRI constant in `V`. -/
def ConclOK (V : Set Iri) (prem : PGraph Var Iri Lit) (concl : Option (PTriple Var Iri Lit)) :
    Prop :=
  ∀ c, concl = some c → ∀ z ∈ c.terms, (∃ t ∈ prem, z ∈ t.terms) ∨ ∃ v ∈ V, z = PTerm.iri v

theorem conclOK_range {prem : PGraph Var Iri Lit} {c : PTriple Var Iri Lit}
    (hc : ∀ z ∈ c.terms, (∃ t ∈ prem, z ∈ t.terms) ∨ ∃ v ∈ V, z = PTerm.iri v)
    (θ : Var → Term Iri Lit Bn) :
    ∀ x ∈ (c.map (PTerm.eval θ)).terms,
      x ∈ (prem.inst θ).terms ∨ ∃ v ∈ V, x = Term.iri v := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (Triple.mem_terms_map _ _).1 hx
  rcases hc z hz with ⟨t, ht, hzt⟩ | ⟨v, hv, rfl⟩
  · exact Or.inl ⟨t.map (PTerm.eval θ), ⟨t, ht, rfl⟩,
      (Triple.mem_terms_map _ _).2 ⟨z, hzt, rfl⟩⟩
  · exact Or.inr ⟨v, hv, rfl⟩

theorem conclOK_const {prem : PGraph Var Iri Lit} (hprem : prem.Over V)
    {c : PTriple Var Iri Lit}
    (hc : ∀ z ∈ c.terms, (∃ t ∈ prem, z ∈ t.terms) ∨ ∃ v ∈ V, z = PTerm.iri v) :
    ∀ z ∈ c.terms, z.Const V := by
  intro z hz
  rcases hc z hz with ⟨t, ht, hzt⟩ | ⟨v, hv, rfl⟩
  · exact hprem t ht z hzt
  · exact hv

/-- A map fixing `L ∪ V` commutes with instantiation of a conclusion. -/
theorem option_map_eval {ρ : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (θ : Var → Term Iri Lit Bn) {prem : PGraph Var Iri Lit} (hprem : prem.Over V)
    {concl : Option (PTriple Var Iri Lit)} (hconcl : ConclOK V prem concl) :
    Option.map (Triple.map ρ) (Option.map (Triple.map (PTerm.eval θ)) concl) =
      Option.map (Triple.map (PTerm.eval (fun x => ρ (θ x)))) concl := by
  cases hc : concl with
  | none => rfl
  | some c =>
    show some (Triple.map ρ (c.map (PTerm.eval θ))) = some _
    rw [map_eval_triple hρ θ (conclOK_const hprem (hconcl c hc))]

/-- Instantiation of a conclusion depends only on the values of the premise variables. -/
theorem option_map_congr {prem : PGraph Var Iri Lit} {concl : Option (PTriple Var Iri Lit)}
    (hconcl : ConclOK V prem concl) {θ θ' : Var → Term Iri Lit Bn}
    (h : ∀ x ∈ prem.vars, θ x = θ' x) :
    Option.map (Triple.map (PTerm.eval θ)) concl =
      Option.map (Triple.map (PTerm.eval θ')) concl := by
  cases hc : concl with
  | none => rfl
  | some c =>
    show some (c.map (PTerm.eval θ)) = some (c.map (PTerm.eval θ'))
    congr 1
    refine Triple.map_congr (fun z hz => ?_)
    rcases hconcl c hc z hz with ⟨t, ht, hzt⟩ | ⟨v, -, rfl⟩
    · cases z with
      | var x => exact h x ⟨t, ht, hzt⟩
      | iri v => rfl
      | lit l => rfl
    · rfl

/-! ## Guards -/

/-- A guard is invariant over the variables `P` when it is preserved by any `ρ` fixing
`L ∪ V` that is undone on the values of `P` by another map fixing `L ∪ V`. -/
def GuardInvariant (V : Set Iri) (P : Set Var) (g : (Var → Term Iri Lit Bn) → Prop) : Prop :=
  ∀ (θ : Var → Term Iri Lit Bn) (ρ ρ' : Term Iri Lit Bn → Term Iri Lit Bn),
    FixesLV V ρ → FixesLV V ρ' → (∀ x ∈ P, ρ' (ρ (θ x)) = θ x) → g θ → g (fun x => ρ (θ x))

theorem guardInvariant_true (P : Set Var) :
    GuardInvariant V P (fun _ : Var → Term Iri Lit Bn => True) :=
  fun _ _ _ _ _ _ h => h

theorem GuardInvariant.and {P : Set Var} {g₁ g₂ : (Var → Term Iri Lit Bn) → Prop}
    (h₁ : GuardInvariant V P g₁) (h₂ : GuardInvariant V P g₂) :
    GuardInvariant V P (fun θ => g₁ θ ∧ g₂ θ) :=
  fun θ ρ ρ' hρ hρ' hinv h => ⟨h₁ θ ρ ρ' hρ hρ' hinv h.1, h₂ θ ρ ρ' hρ hρ' hinv h.2⟩

theorem GuardInvariant.or {P : Set Var} {g₁ g₂ : (Var → Term Iri Lit Bn) → Prop}
    (h₁ : GuardInvariant V P g₁) (h₂ : GuardInvariant V P g₂) :
    GuardInvariant V P (fun θ => g₁ θ ∨ g₂ θ) :=
  fun θ ρ ρ' hρ hρ' hinv h =>
    h.elim (fun h => Or.inl (h₁ θ ρ ρ' hρ hρ' hinv h)) (fun h => Or.inr (h₂ θ ρ ρ' hρ hρ' hinv h))

/-- Invariance over fewer variables is the stronger property. -/
theorem GuardInvariant.mono {P Q : Set Var} {g : (Var → Term Iri Lit Bn) → Prop}
    (hPQ : P ⊆ Q) (h : GuardInvariant V P g) : GuardInvariant V Q g :=
  fun θ ρ ρ' hρ hρ' hinv hg => h θ ρ ρ' hρ hρ' (fun x hx => hinv x (hPQ hx)) hg

/-- The projection of a guard onto the variables `P`: some substitution agreeing with `θ`
on `P` satisfies the guard. -/
def projGuard (P : Set Var) (g : (Var → Term Iri Lit Bn) → Prop)
    (θ : Var → Term Iri Lit Bn) : Prop :=
  ∃ θ' : Var → Term Iri Lit Bn, (∀ x ∈ P, θ' x = θ x) ∧ g θ'

/-- An invariant guard has an invariant projection. -/
theorem GuardInvariant.proj {P : Set Var} {g : (Var → Term Iri Lit Bn) → Prop}
    (h : GuardInvariant V P g) : GuardInvariant V P (projGuard P g) := by
  rintro θ ρ ρ' hρ hρ' hinv ⟨θ', hag, hg⟩
  refine ⟨fun x => ρ (θ' x), fun x hx => ?_, h θ' ρ ρ' hρ hρ' (fun x hx => ?_) hg⟩
  · show ρ (θ' x) = ρ (θ x)
    rw [hag x hx]
  · rw [hag x hx]
    exact hinv x hx

/-- The guard "`x` and `y` are bound to literals `l`, `m` with `R l m`". -/
def litGuard (R : Lit → Lit → Prop) (x y : Var) (θ : Var → Term Iri Lit Bn) : Prop :=
  ∃ l m, θ x = Term.lit l ∧ θ y = Term.lit m ∧ R l m

/-- A comparison between literal values is invariant, over any set of variables: maps
fixing `L ∪ V` fix every literal. -/
theorem guardInvariant_lit (P : Set Var) (R : Lit → Lit → Prop) (x y : Var) :
    GuardInvariant V P (litGuard (Iri := Iri) (Bn := Bn) R x y) := by
  rintro θ ρ ρ' hρ - - ⟨l, m, hx, hy, hR⟩
  refine ⟨l, m, ?_, ?_, hR⟩
  · show ρ (θ x) = Term.lit l
    rw [hx]
    exact hρ.1 l
  · show ρ (θ y) = Term.lit m
    rw [hy]
    exact hρ.1 m

/-- The literal a term is, if it is one. -/
def Term.litView : Term Iri Lit Bn → Option Lit
  | Term.lit l => some l
  | _ => none

/-- A renaming does not turn a non-literal into a literal. -/
theorem litView_rename {ρ ρ' : Term Iri Lit Bn → Term Iri Lit Bn} (hρ : FixesLV V ρ)
    (hρ' : FixesLV V ρ') {t : Term Iri Lit Bn} (h : ρ' (ρ t) = t) :
    (ρ t).litView = t.litView := by
  cases t with
  | lit l => rw [hρ.1 l]
  | iri a =>
    cases hr : ρ (Term.iri a) with
    | lit l =>
      rw [hr, hρ'.1 l] at h
      cases h
    | iri b => rfl
    | bnode b => rfl
  | bnode a =>
    cases hr : ρ (Term.bnode a) with
    | lit l =>
      rw [hr, hρ'.1 l] at h
      cases h
    | iri b => rfl
    | bnode b => rfl

/-- Any guard that depends only on which literals the variables in `P` are bound to
(including which of them are not literals) is invariant over `P`. -/
theorem guardInvariant_litView {P : Set Var} (Q : (Var → Option Lit) → Prop)
    (hQ : ∀ f f' : Var → Option Lit, (∀ x ∈ P, f x = f' x) → Q f → Q f') :
    GuardInvariant V P (fun θ : Var → Term Iri Lit Bn => Q (fun x => (θ x).litView)) := by
  intro θ ρ ρ' hρ hρ' hinv h
  exact hQ _ _ (fun x hx => (litView_rename hρ hρ' (hinv x hx)).symm) h

/-- The guard `X ≠ Y`. -/
def neGuard (x y : Var) (θ : Var → Term Iri Lit Bn) : Prop := θ x ≠ θ y

/-- `X ≠ Y` is invariant when both variables are among `P`: a renaming is injective on
their values. -/
theorem guardInvariant_ne {P : Set Var} {x y : Var} (hx : x ∈ P) (hy : y ∈ P) :
    GuardInvariant V P (neGuard (Iri := Iri) (Lit := Lit) (Bn := Bn) x y) := by
  intro θ ρ ρ' _ _ hinv hne
  show ρ (θ x) ≠ ρ (θ y)
  intro heq
  apply hne
  have h : ρ' (ρ (θ x)) = ρ' (ρ (θ y)) := congrArg ρ' heq
  rwa [hinv x hx, hinv y hy] at h

/-- The guard `X ≠ k` for a fixed term `k`. -/
def neConstGuard (x : Var) (k : Term Iri Lit Bn) (θ : Var → Term Iri Lit Bn) : Prop := θ x ≠ k

/-- `X ≠ k` is invariant when `X` is among `P` and `k` is fixed by every map fixing
`L ∪ V` (a literal, or an IRI in `V`). -/
theorem guardInvariant_neConst {P : Set Var} {x : Var} (hx : x ∈ P) {k : Term Iri Lit Bn}
    (hk : ∀ ρ : Term Iri Lit Bn → Term Iri Lit Bn, FixesLV V ρ → ρ k = k) :
    GuardInvariant V P (neConstGuard x k) := by
  intro θ ρ ρ' _ hρ' hinv hne
  show ρ (θ x) ≠ k
  intro heq
  apply hne
  have h : ρ' (ρ (θ x)) = ρ' k := congrArg ρ' heq
  rwa [hinv x hx, hk ρ' hρ'] at h

open Classical in
/-- The condition has teeth: a guard that tests whether a variable is bound to a blank node
is not invariant, even over that variable.  A renaming may exchange a blank node and an IRI
outside `V`, as Skolemization does.  So no well-formed entry can treat Skolem terms or blank
nodes differently from other terms. -/
theorem not_guardInvariant_isBnode (x : Var) (b : Bn) {a : Iri} (ha : a ∉ V) :
    ¬ GuardInvariant V ({x} : Set Var)
      (fun θ : Var → Term Iri Lit Bn => ∃ b' : Bn, θ x = Term.bnode b') := by
  intro h
  let ρ : Term Iri Lit Bn → Term Iri Lit Bn :=
    fun t => if t = Term.bnode b then Term.iri a else t
  let ρ' : Term Iri Lit Bn → Term Iri Lit Bn :=
    fun t => if t = Term.iri a then Term.bnode b else t
  have hρ : FixesLV V ρ :=
    ⟨fun l => ite_eq_right (by intro h; cases h), fun v _ => ite_eq_right (by intro h; cases h)⟩
  have hρ' : FixesLV V ρ' :=
    ⟨fun l => ite_eq_right (by intro h; cases h),
      fun v hv => ite_eq_right (by intro h; exact ha (Term.iri.inj h ▸ hv))⟩
  have h1 : ρ (Term.bnode b) = Term.iri a := ite_eq_left rfl
  have hinv : ∀ y ∈ ({x} : Set Var),
      ρ' (ρ ((fun _ : Var => (Term.bnode b : Term Iri Lit Bn)) y)) =
        (fun _ : Var => (Term.bnode b : Term Iri Lit Bn)) y := by
    intro y _
    show ρ' (ρ (Term.bnode b)) = Term.bnode b
    rw [h1]
    exact ite_eq_left rfl
  obtain ⟨b', hb'⟩ := h (fun _ => Term.bnode b) ρ ρ' hρ hρ' hinv ⟨b, rfl⟩
  have h2 : (Term.iri a : Term Iri Lit Bn) = Term.bnode b' := h1.symm.trans hb'
  cases h2

/-! ## Pattern entries -/

/-- A pattern entry `⟨A, c; E⟩` with a guard. -/
structure PEntry (Var Iri Lit Bn : Type) where
  /-- The premises. -/
  prem : PGraph Var Iri Lit
  /-- The conclusion; `none` is `⊥`. -/
  concl : Option (PTriple Var Iri Lit)
  /-- The defeaters.  Variables not in the premises are read existentially. -/
  defeaters : Set (PGraph Var Iri Lit)
  /-- The guard, a predicate on substitutions. -/
  guard : (Var → Term Iri Lit Bn) → Prop

/-- The ground instance of a pattern entry at `θ`.  Its defeaters are all instances `D·η`
with `η` agreeing with `θ` on the premise variables. -/
def PEntry.inst (e : PEntry Var Iri Lit Bn) (θ : Var → Term Iri Lit Bn) : Entry Iri Lit Bn where
  prem := e.prem.inst θ
  concl := e.concl.map (Triple.map (PTerm.eval θ))
  defeaters := {D' | ∃ D ∈ e.defeaters, ∃ η : Var → Term Iri Lit Bn,
    (∀ x ∈ e.prem.vars, η x = θ x) ∧ D' = D.inst η}

/-- Well-formedness of a pattern entry over `V`. -/
structure PEntry.WF (V : Set Iri) (e : PEntry Var Iri Lit Bn) : Prop where
  /-- (1) IRI constants of the premises are in `V`. -/
  prem : e.prem.Over V
  /-- (2) Each term of the conclusion occurs in the premises or is an IRI constant in `V`. -/
  concl : ConclOK V e.prem e.concl
  /-- (3) IRI constants of the defeaters are in `V`. -/
  defeaters : ∀ D ∈ e.defeaters, D.Over V
  /-- (4) The projection of the guard onto the premise variables is invariant. -/
  guard : GuardInvariant V e.prem.vars (projGuard e.prem.vars e.guard)

/-- **Pattern entries form an `Entries`.** The ground instances of a set of well-formed
pattern entries, one per substitution satisfying the guard, are range-restricted and closed
under renamings. -/
def patternEntries (S : Set (PEntry Var Iri Lit Bn)) (hS : ∀ e ∈ S, e.WF V) :
    Entries Iri Lit Bn V where
  entries := {g | ∃ e ∈ S, ∃ θ : Var → Term Iri Lit Bn, e.guard θ ∧ g = e.inst θ}
  range := by
    rintro _ ⟨e, he, θ, -, rfl⟩ c' hc' x hx
    have hc'' : Option.map (Triple.map (PTerm.eval θ)) e.concl = some c' := hc'
    cases hc : e.concl with
    | none =>
      rw [hc] at hc''
      cases hc''
    | some c =>
      rw [hc] at hc''
      have h2 : c.map (PTerm.eval θ) = c' := Option.some.inj hc''
      rw [← h2] at hx
      exact conclOK_range ((hS e he).concl c hc) θ x hx
  uniform := by
    rintro ρ ρ' hρ hρ' _ ⟨e, he, θ, hg, rfl⟩ hinv
    have hwf := hS e he
    have hθ : ∀ x ∈ e.prem.vars, ρ' (ρ (θ x)) = θ x := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := PGraph.eval_mem_terms_inst θ hx
      exact hinv t ht (θ x) hxt
    -- the renamed premise bindings extend to a substitution satisfying the guard
    obtain ⟨θ₂, hag, hg₂⟩ := hwf.guard θ ρ ρ' hρ hρ' hθ ⟨θ, fun _ _ => rfl, hg⟩
    have hag' : ∀ x ∈ e.prem.vars, θ₂ x = ρ (θ x) := hag
    refine ⟨e.inst θ₂, ⟨e, he, θ₂, hg₂, rfl⟩, ?_, ?_, ?_⟩
    · show e.prem.inst θ₂ = Graph.mapT ρ (e.prem.inst θ)
      rw [PGraph.mapT_inst hρ θ hwf.prem]
      exact PGraph.inst_congr hag'
    · show Option.map (Triple.map (PTerm.eval θ₂)) e.concl =
        Option.map (Triple.map ρ) (Option.map (Triple.map (PTerm.eval θ)) e.concl)
      rw [option_map_eval hρ θ hwf.prem hwf.concl]
      exact option_map_congr hwf.concl hag'
    · rintro _ ⟨D, hD, η, hη, rfl⟩
      refine ⟨D, hD, fun x => ρ' (η x), ?_, PGraph.mapT_inst hρ' η (hwf.defeaters D hD)⟩
      intro x hx
      show ρ' (η x) = θ x
      rw [hη x hx, hag' x hx]
      exact hθ x hx

theorem mem_patternEntries {S : Set (PEntry Var Iri Lit Bn)} {hS : ∀ e ∈ S, e.WF V}
    {g : Entry Iri Lit Bn} :
    g ∈ (patternEntries S hS).entries ↔
      ∃ e ∈ S, ∃ θ : Var → Term Iri Lit Bn, e.guard θ ∧ g = e.inst θ :=
  Iff.rfl

/-- A ground instance applies at `K` when the instantiated premises are in `K` and no
defeater has an instance in `K` extending the premise bindings. -/
theorem PEntry.applies_inst_iff (e : PEntry Var Iri Lit Bn) (θ : Var → Term Iri Lit Bn)
    (K : Graph Iri Lit Bn) :
    (e.inst θ).Applies K ↔
      e.prem.inst θ ⊆ K ∧ ∀ D ∈ e.defeaters, ∀ η : Var → Term Iri Lit Bn,
        (∀ x ∈ e.prem.vars, η x = θ x) → ¬ D.inst η ⊆ K := by
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨hp, fun D hD η hη => hd _ ⟨D, hD, η, hη, rfl⟩⟩
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    rintro _ ⟨D, hD, η, hη, rfl⟩
    exact hd D hD η hη

/-- Over the empty regime, `Cons(X)` is `X` with one round of defaults. -/
theorem emptyRegime_entriesBase_cons (E : Entries Iri Lit Bn V) (X : Graph Iri Lit Bn) :
    ((emptyRegime Iri Lit Bn V).entriesBase E).cons X = X ∪ E.dstar X := by
  rw [Regime.entriesBase_cons]
  simp only [emptyRegime_clPos]

/-- Over the empty regime, incoherence is the application of an incompatibility entry. -/
theorem emptyRegime_entriesBase_inc (E : Entries Iri Lit Bn V) (X : Graph Iri Lit Bn) :
    ((emptyRegime Iri Lit Bn V).entriesBase E).inc X ↔ E.Incompat X := by
  rw [Regime.entriesBase_inc, emptyRegime_clPos]
  exact ⟨fun h => h.resolve_left (emptyRegime_not_inconsistent V X), Or.inr⟩

/-! ## Pattern rules -/

/-- A pattern rule `⟨A, c⟩`: positive patterns, no defeaters, no guard. -/
structure PRule (Var Iri Lit : Type) where
  prem : PGraph Var Iri Lit
  concl : Option (PTriple Var Iri Lit)

/-- The ground instance of a pattern rule at `θ`. -/
def PRule.inst (r : PRule Var Iri Lit) (θ : Var → Term Iri Lit Bn) : Rule Iri Lit Bn :=
  ⟨r.prem.inst θ, r.concl.map (Triple.map (PTerm.eval θ))⟩

/-- Well-formedness of a pattern rule over `V`. -/
structure PRule.WF (V : Set Iri) (r : PRule Var Iri Lit) : Prop where
  prem : r.prem.Over V
  concl : ConclOK V r.prem r.concl

/-- **Pattern rules form a `Regime`.** The ground instances of a set of well-formed pattern
rules satisfy range restriction and uniformity (Definition 4). -/
def patternRegime (S : Set (PRule Var Iri Lit)) (hS : ∀ r ∈ S, r.WF V) :
    Regime Iri Lit Bn V where
  rules := {g | ∃ r ∈ S, ∃ θ : Var → Term Iri Lit Bn, g = r.inst θ}
  range := by
    rintro _ ⟨r, hr, θ, rfl⟩ c' hc' x hx
    have hc'' : Option.map (Triple.map (PTerm.eval θ)) r.concl = some c' := hc'
    cases hc : r.concl with
    | none =>
      rw [hc] at hc''
      cases hc''
    | some c =>
      rw [hc] at hc''
      have h2 : c.map (PTerm.eval θ) = c' := Option.some.inj hc''
      rw [← h2] at hx
      rcases conclOK_range ((hS r hr).concl c hc) θ x hx with h | h
      · exact Or.inl h
      · exact Or.inr h
  uniform := by
    rintro ρ hρ _ ⟨r, hr, θ, rfl⟩
    refine ⟨r, hr, fun x => ρ (θ x), ?_⟩
    show Rule.mk (Graph.mapT ρ (r.prem.inst θ))
        (Option.map (Triple.map ρ) (Option.map (Triple.map (PTerm.eval θ)) r.concl)) =
      Rule.mk (r.prem.inst (fun x => ρ (θ x)))
        (Option.map (Triple.map (PTerm.eval (fun x => ρ (θ x)))) r.concl)
    rw [PGraph.mapT_inst hρ θ (hS r hr).prem, option_map_eval hρ θ (hS r hr).prem (hS r hr).concl]

/-! ## The shapes of the Wikidata case study -/

namespace Shapes

/-- Five variables, enough for the shapes below. -/
inductive Vr
  | X | Y | C | E | S

open PTerm (var iri lit)

/-- The triple pattern `s p o` with a constant IRI predicate. -/
abbrev pt (s : PTerm Vr Iri Lit) (p : Iri) (o : PTerm Vr Iri Lit) : PTriple Vr Iri Lit :=
  ⟨s, PTerm.iri p, o⟩

theorem pt_const {s o : PTerm Vr Iri Lit} {p : Iri} (hs : s.Const V) (hp : p ∈ V)
    (ho : o.Const V) : ∀ z ∈ (pt s p o).terms, z.Const V :=
  PGraph.const_terms hs hp ho

/-- The variables of the one-premise pattern `{X p Y}` are `X` and `Y`. -/
theorem vars_xy {p : Iri} {x : Vr}
    (hx : x ∈ PGraph.vars ({pt (var Vr.X) p (var Vr.Y)} : PGraph Vr Iri Lit)) :
    x = Vr.X ∨ x = Vr.Y := by
  obtain ⟨t, ht, hxt⟩ := hx
  rw [Set.mem_singleton_iff.1 ht] at hxt
  simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hxt
  rcases hxt with h | h | h
  · exact Or.inl (PTerm.var.inj h)
  · cases h
  · exact Or.inr (PTerm.var.inj h)

variable {p t k s u K e d b : Iri}

/-! ### (a) An incompatibility with several defeaters -/

/-- `{X p Y}` gives `⊥` unless `{X t T}` for some `T` in `Ts`: "the subject of `p` must
have one of the types `Ts`". -/
def typeEntry (p t : Iri) (Ts : Set Iri) : PEntry Vr Iri Lit Bn where
  prem := {pt (var Vr.X) p (var Vr.Y)}
  concl := none
  defeaters := {D | ∃ T ∈ Ts, D = {pt (var Vr.X) t (iri T)}}
  guard := fun _ => True

theorem typeEntry_wf (hp : p ∈ V) (ht : t ∈ V) {Ts : Set Iri} (hTs : Ts ⊆ V) :
    (typeEntry p t Ts : PEntry Vr Iri Lit Bn).WF V where
  prem := PGraph.over_singleton (pt_const trivial hp trivial)
  concl := by
    intro c hc
    cases hc
  defeaters := by
    rintro _ ⟨T, hT, rfl⟩
    exact PGraph.over_singleton (pt_const trivial ht (hTs hT))
  guard := (guardInvariant_true _).proj

/-- The base of `typeEntry` over the empty regime. -/
abbrev typeBase (hp : p ∈ V) (ht : t ∈ V) {Ts : Set Iri} (hTs : Ts ⊆ V) :
    ConsBase Iri Lit Bn V :=
  (emptyRegime Iri Lit Bn V).entriesBase
    (patternEntries {typeEntry p t Ts} (by
      intro e he
      rw [Set.mem_singleton_iff.1 he]
      exact typeEntry_wf hp ht hTs))

/-- Shape (a) in use: an untyped subject is incoherent, and adding one of the allowed types
removes the incoherence.  Incoherence from an entry with defeaters is not monotone. -/
theorem type_incoherence_lost (hp : p ∈ V) (ht : t ∈ V) {Ts : Set Iri} (hTs : Ts ⊆ V)
    (htp : t ≠ p) {T : Iri} (hT : T ∈ Ts) (a c : Term Iri Lit Bn) :
    (typeBase hp ht hTs).inc {tri a p c} ∧
      ¬ (typeBase hp ht hTs).inc ({tri a p c} ∪ {tri a t (Term.iri T)}) := by
  constructor
  · rw [emptyRegime_entriesBase_inc]
    refine ⟨(typeEntry p t Ts).inst (fun v => match v with | Vr.X => a | _ => c),
      ⟨typeEntry p t Ts, Set.mem_singleton _, _, trivial, rfl⟩, ⟨?_, ?_⟩, rfl⟩
    · rintro _ ⟨t', ht', rfl⟩
      rw [Set.mem_singleton_iff.1 ht']
      exact Set.mem_singleton _
    · rintro _ ⟨D, ⟨T', -, rfl⟩, η, -, rfl⟩ hsub
      have h1 : tri (η Vr.X) t (Term.iri T') ∈ ({tri a p c} : Graph Iri Lit Bn) :=
        hsub ⟨pt (var Vr.X) t (iri T'), Set.mem_singleton _, rfl⟩
      exact htp (tri_inj.1 (Set.mem_singleton_iff.1 h1)).2.1
  · rw [emptyRegime_entriesBase_inc]
    rintro ⟨_, ⟨e', he', θ, -, rfl⟩, ha, -⟩
    rw [Set.mem_singleton_iff.1 he'] at ha
    have hprem : tri (θ Vr.X) p (θ Vr.Y) ∈
        ({tri a p c} ∪ {tri a t (Term.iri T)} : Graph Iri Lit Bn) :=
      ha.1 ⟨pt (var Vr.X) p (var Vr.Y), Set.mem_singleton _, rfl⟩
    have hX : θ Vr.X = a := by
      rcases hprem with h | h
      · exact (tri_inj.1 (Set.mem_singleton_iff.1 h)).1
      · exact (tri_inj.1 (Set.mem_singleton_iff.1 h)).1
    refine ha.2 _ ⟨{pt (var Vr.X) t (iri T)}, ⟨T, hT, rfl⟩, θ, fun _ _ => rfl, rfl⟩ ?_
    rintro _ ⟨t', ht', rfl⟩
    rw [Set.mem_singleton_iff.1 ht']
    show tri (θ Vr.X) t (Term.iri T) ∈ _
    rw [hX]
    exact Or.inr (Set.mem_singleton _)

/-! ### (b) A defeater with an existential variable -/

/-- `{X p Y}` gives `Y p X` unless `{k s C . C u K . C e X}`.  The variable `C` does not
occur in the premises: the default is defeated when *some* `C` completes the pattern. -/
def excEntry (p k s u K e : Iri) : PEntry Vr Iri Lit Bn where
  prem := {pt (var Vr.X) p (var Vr.Y)}
  concl := some (pt (var Vr.Y) p (var Vr.X))
  defeaters := {{pt (iri k) s (var Vr.C), pt (var Vr.C) u (iri K), pt (var Vr.C) e (var Vr.X)}}
  guard := fun _ => True

theorem excEntry_wf (hp : p ∈ V) (hk : k ∈ V) (hs : s ∈ V) (hu : u ∈ V) (hK : K ∈ V)
    (he : e ∈ V) : (excEntry p k s u K e : PEntry Vr Iri Lit Bn).WF V where
  prem := PGraph.over_singleton (pt_const trivial hp trivial)
  concl := by
    intro c hc
    rw [← Option.some.inj hc]
    intro z hz
    refine Or.inl ⟨pt (var Vr.X) p (var Vr.Y), Set.mem_singleton _, ?_⟩
    simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  defeaters := by
    intro D hD
    rw [Set.mem_singleton_iff.1 hD]
    exact PGraph.over_insert (pt_const hk hs trivial)
      (PGraph.over_insert (pt_const trivial hu hK)
        (PGraph.over_singleton (pt_const trivial he trivial)))
  guard := (guardInvariant_true _).proj

/-- The base of `excEntry` over the empty regime. -/
abbrev excBase (hp : p ∈ V) (hk : k ∈ V) (hs : s ∈ V) (hu : u ∈ V) (hK : K ∈ V)
    (he : e ∈ V) : ConsBase Iri Lit Bn V :=
  (emptyRegime Iri Lit Bn V).entriesBase
    (patternEntries {excEntry p k s u K e} (by
      intro e' he'
      rw [Set.mem_singleton_iff.1 he']
      exact excEntry_wf hp hk hs hu hK he))

/-- Shape (b) in use, a concrete defeat: on `{a p b}` the default fires and concludes
`b p a`; once the exception triples `k s c`, `c u K`, `c e a` are added, for any term `c`,
it does not. -/
theorem exc_defeat (hp : p ∈ V) (hk : k ∈ V) (hs : s ∈ V) (hu : u ∈ V) (hK : K ∈ V)
    (he : e ∈ V) (hsp : s ≠ p) (hup : u ≠ p) (hep : e ≠ p) {a b : Term Iri Lit Bn}
    (hab : a ≠ b) (c : Term Iri Lit Bn) :
    tri b p a ∈ (excBase hp hk hs hu hK he).cons {tri a p b} ∧
      tri b p a ∉ (excBase hp hk hs hu hK he).cons
        ({tri a p b} ∪ {tri (Term.iri k) s c, tri c u (Term.iri K), tri c e a}) := by
  constructor
  · rw [emptyRegime_entriesBase_cons]
    refine Or.inr ⟨(excEntry p k s u K e).inst (fun v => match v with | Vr.X => a | _ => b),
      ⟨excEntry p k s u K e, Set.mem_singleton _, _, trivial, rfl⟩, ⟨?_, ?_⟩, rfl⟩
    · rintro _ ⟨t', ht', rfl⟩
      rw [Set.mem_singleton_iff.1 ht']
      exact Set.mem_singleton _
    · rintro _ ⟨D, hD, η, -, rfl⟩ hsub
      rw [Set.mem_singleton_iff.1 hD] at hsub
      have h1 : tri (Term.iri k) s (η Vr.C) ∈ ({tri a p b} : Graph Iri Lit Bn) :=
        hsub ⟨pt (iri k) s (var Vr.C), Set.mem_insert _ _, rfl⟩
      exact hsp (tri_inj.1 (Set.mem_singleton_iff.1 h1)).2.1
  · rw [emptyRegime_entriesBase_cons]
    rintro (h | ⟨_, ⟨e', he', θ, -, rfl⟩, ha, hc⟩)
    · rcases h with h | h
      · exact hab (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.2
      · rcases Set.mem_insert_iff.1 h with h | h
        · exact hsp (tri_inj.1 h).2.1.symm
        · rcases Set.mem_insert_iff.1 h with h | h
          · exact hup (tri_inj.1 h).2.1.symm
          · exact hep (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1.symm
    · rw [Set.mem_singleton_iff.1 he'] at ha hc
      have hc' : tri (θ Vr.Y) p (θ Vr.X) = tri b p a := Option.some.inj hc
      have hX : θ Vr.X = a := (tri_inj.1 hc').2.2
      refine ha.2 _ ⟨_, Set.mem_singleton _, fun v => match v with | Vr.C => c | v => θ v,
        ?_, rfl⟩ ?_
      · intro x hx
        rcases vars_xy hx with h | h
        · rw [h]
        · rw [h]
      · rintro _ ⟨t', ht', rfl⟩
        rcases Set.mem_insert_iff.1 ht' with h | h
        · rw [h]
          exact Or.inr (Or.inl rfl)
        · rcases Set.mem_insert_iff.1 h with h | h
          · rw [h]
            exact Or.inr (Or.inr (Or.inl rfl))
          · rw [Set.mem_singleton_iff.1 h]
            show tri c e (θ Vr.X) ∈ _
            rw [hX]
            exact Or.inr (Or.inr (Or.inr (Set.mem_singleton _)))

/-! ### (c) Several premises with a literal guard -/

/-- `{X p Y . X d E . Y b S}` gives `⊥` when `E` and `S` are literals with `lt E S`. -/
def contempEntry (p d b : Iri) (lt : Lit → Lit → Prop) : PEntry Vr Iri Lit Bn where
  prem := {pt (var Vr.X) p (var Vr.Y), pt (var Vr.X) d (var Vr.E), pt (var Vr.Y) b (var Vr.S)}
  concl := none
  defeaters := ∅
  guard := litGuard lt Vr.E Vr.S

theorem contempEntry_wf (hp : p ∈ V) (hd : d ∈ V) (hb : b ∈ V) (lt : Lit → Lit → Prop) :
    (contempEntry p d b lt : PEntry Vr Iri Lit Bn).WF V where
  prem := PGraph.over_insert (pt_const trivial hp trivial)
    (PGraph.over_insert (pt_const trivial hd trivial)
      (PGraph.over_singleton (pt_const trivial hb trivial)))
  concl := by
    intro c hc
    cases hc
  defeaters := fun _ hD => (Set.notMem_empty _ hD).elim
  guard := (guardInvariant_lit _ lt Vr.E Vr.S).proj

/-- The base of `contempEntry` over the empty regime. -/
abbrev contempBase (hp : p ∈ V) (hd : d ∈ V) (hb : b ∈ V) (lt : Lit → Lit → Prop) :
    ConsBase Iri Lit Bn V :=
  (emptyRegime Iri Lit Bn V).entriesBase
    (patternEntries {contempEntry p d b lt} (by
      intro e' he'
      rw [Set.mem_singleton_iff.1 he']
      exact contempEntry_wf hp hd hb lt))

/-- Shape (c) in use: with `p`, `d`, `b` distinct, the graph `{x p y, x d l, y b m}` on
literals `l`, `m` is incoherent exactly when `lt l m`. -/
theorem contemp_inc_iff (hp : p ∈ V) (hd : d ∈ V) (hb : b ∈ V) (lt : Lit → Lit → Prop)
    (hpd : p ≠ d) (hpb : p ≠ b) (hdb : d ≠ b) (x y : Term Iri Lit Bn) (l m : Lit) :
    (contempBase hp hd hb lt).inc
        {tri x p y, tri x d (Term.lit l), tri y b (Term.lit m)} ↔ lt l m := by
  rw [emptyRegime_entriesBase_inc]
  constructor
  · rintro ⟨_, ⟨e', he', θ, hg, rfl⟩, ha, -⟩
    rw [Set.mem_singleton_iff.1 he'] at ha hg
    obtain ⟨l', m', hE, hS, hlt⟩ := hg
    have h2 : tri (θ Vr.X) d (θ Vr.E) ∈
        ({tri x p y, tri x d (Term.lit l), tri y b (Term.lit m)} : Graph Iri Lit Bn) :=
      ha.1 ⟨pt (var Vr.X) d (var Vr.E), Set.mem_insert_of_mem _ (Set.mem_insert _ _), rfl⟩
    have h3 : tri (θ Vr.Y) b (θ Vr.S) ∈
        ({tri x p y, tri x d (Term.lit l), tri y b (Term.lit m)} : Graph Iri Lit Bn) :=
      ha.1 ⟨pt (var Vr.Y) b (var Vr.S),
        Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩
    have hEl : θ Vr.E = Term.lit l := by
      rcases Set.mem_insert_iff.1 h2 with h | h
      · exact (hpd (tri_inj.1 h).2.1.symm).elim
      · rcases Set.mem_insert_iff.1 h with h | h
        · exact (tri_inj.1 h).2.2
        · exact (hdb (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1).elim
    have hSm : θ Vr.S = Term.lit m := by
      rcases Set.mem_insert_iff.1 h3 with h | h
      · exact (hpb (tri_inj.1 h).2.1.symm).elim
      · rcases Set.mem_insert_iff.1 h with h | h
        · exact (hdb (tri_inj.1 h).2.1.symm).elim
        · exact (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.2
    rw [hEl] at hE
    rw [hSm] at hS
    rw [Term.lit.inj hE, Term.lit.inj hS]
    exact hlt
  · intro hlt
    refine ⟨(contempEntry p d b lt).inst
        (fun v => match v with
          | Vr.X => x | Vr.Y => y | Vr.E => Term.lit l | Vr.S => Term.lit m | Vr.C => x),
      ⟨contempEntry p d b lt, Set.mem_singleton _, _, ⟨l, m, rfl, rfl, hlt⟩, rfl⟩,
      ⟨?_, ?_⟩, rfl⟩
    · rintro _ ⟨t', ht', rfl⟩
      rcases Set.mem_insert_iff.1 ht' with h | h
      · rw [h]
        exact Set.mem_insert _ _
      · rcases Set.mem_insert_iff.1 h with h | h
        · rw [h]
          exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · rw [Set.mem_singleton_iff.1 h]
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rintro _ ⟨D, hD, -⟩
      exact (Set.notMem_empty _ hD).elim

/-! ### The regime of the case study, and its base -/

variable {sub ins : Iri}

/-- `{X sub Y . Y sub C}` gives `X sub C`: `sub` is transitive. -/
def subTransRule (sub : Iri) : PRule Vr Iri Lit :=
  ⟨{pt (var Vr.X) sub (var Vr.Y), pt (var Vr.Y) sub (var Vr.C)},
    some (pt (var Vr.X) sub (var Vr.C))⟩

/-- `{X ins Y . Y sub C}` gives `X ins C`: `ins` passes up `sub`. -/
def instUpRule (ins sub : Iri) : PRule Vr Iri Lit :=
  ⟨{pt (var Vr.X) ins (var Vr.Y), pt (var Vr.Y) sub (var Vr.C)},
    some (pt (var Vr.X) ins (var Vr.C))⟩

theorem subTransRule_wf (hsub : sub ∈ V) : (subTransRule sub : PRule Vr Iri Lit).WF V where
  prem := PGraph.over_insert (pt_const trivial hsub trivial)
    (PGraph.over_singleton (pt_const trivial hsub trivial))
  concl := by
    intro c hc
    rw [← Option.some.inj hc]
    intro z hz
    simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h
    · exact Or.inl ⟨pt (var Vr.X) sub (var Vr.Y), Set.mem_insert _ _, by
        rw [h]; simp [Triple.terms]⟩
    · exact Or.inr ⟨sub, hsub, h⟩
    · exact Or.inl ⟨pt (var Vr.Y) sub (var Vr.C),
        Set.mem_insert_of_mem _ (Set.mem_singleton _), by rw [h]; simp [Triple.terms]⟩

theorem instUpRule_wf (hins : ins ∈ V) (hsub : sub ∈ V) :
    (instUpRule ins sub : PRule Vr Iri Lit).WF V where
  prem := PGraph.over_insert (pt_const trivial hins trivial)
    (PGraph.over_singleton (pt_const trivial hsub trivial))
  concl := by
    intro c hc
    rw [← Option.some.inj hc]
    intro z hz
    simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h
    · exact Or.inl ⟨pt (var Vr.X) ins (var Vr.Y), Set.mem_insert _ _, by
        rw [h]; simp [Triple.terms]⟩
    · exact Or.inr ⟨ins, hins, h⟩
    · exact Or.inl ⟨pt (var Vr.Y) sub (var Vr.C),
        Set.mem_insert_of_mem _ (Set.mem_singleton _), by rw [h]; simp [Triple.terms]⟩

/-- The regime of the case study: `sub` is transitive and `ins` passes up `sub`. -/
def caseRegime (hins : ins ∈ V) (hsub : sub ∈ V) : Regime Iri Lit Bn V :=
  patternRegime {subTransRule sub, instUpRule ins sub} (by
    intro r hr
    rcases Set.mem_insert_iff.1 hr with h | h
    · rw [h]
      exact subTransRule_wf hsub
    · rw [Set.mem_singleton_iff.1 h]
      exact instUpRule_wf hins hsub)

/-- The base of the case study: the two rules together with any set of well-formed pattern
entries.  It is a `ConsBase`, so the general theorem applies to it. -/
def caseBase (hins : ins ∈ V) (hsub : sub ∈ V) (S : Set (PEntry Vr Iri Lit Bn))
    (hS : ∀ e ∈ S, e.WF V) : ConsBase Iri Lit Bn V :=
  (caseRegime hins hsub).entriesBase (patternEntries S hS)

end Shapes

end ISRDF
