import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Function

/-!
# Implication-Space Semantics for RDF — Lean formalization, Part 1: RDF

Formalization of B. P. Allen, "Implication-Space Semantics for RDF" (draft of 6 Sept 2026).
Numbered Definitions/Lemmas/Theorems refer to the note.

Conventions that differ from the note:
* Graphs are `Set`s of triples rather than finite sets. No proof below uses finiteness
  (the note needs it only for the finitary presentation of the role operations).
* The vocabulary fragment `N` (Convention 1) is a set of *names* (non-blank terms),
  not assumed finite.
* Instance mappings are total functions `Bn → Term`; "a mapping `bnodes(H) → N`" becomes
  the predicate `IMap N H` (in Part 2).
* The closure `cl_R` is an inductive predicate `Cl R X : Option Triple → Prop`, with
  `none` playing the role of `⊥`.
-/

set_option autoImplicit false

namespace ISRDF

/-! ## §2  RDF for logical expressivists -/

section Syntax
variable (Iri Lit Bn : Type)

/-- Definition 1: the elements of `I ∪ B ∪ L`. -/
inductive Term
  | iri   (x : Iri)
  | lit   (x : Lit)
  | bnode (b : Bn)

/-- A triple over an arbitrary carrier; over `Term` it is a (generalized) RDF triple,
over a set of objects it is a bearer `T⟨s,p,o⟩` (Definition 9). -/
structure Triple (α : Type) where
  s : α
  p : α
  o : α
end Syntax

variable {Iri Lit Bn : Type}

namespace Term
/-- A name is an IRI or a literal (Definition 1). -/
def IsName : Term Iri Lit Bn → Prop
  | bnode _ => False
  | _       => True

/-- Extension of an instance mapping `μ : B → I ∪ B ∪ L` to terms (Definition 2). -/
def subst (μ : Bn → Term Iri Lit Bn) : Term Iri Lit Bn → Term Iri Lit Bn
  | bnode b => μ b
  | t       => t

@[simp] theorem subst_iri (μ : Bn → Term Iri Lit Bn) (x : Iri) : subst μ (iri x) = iri x := rfl
@[simp] theorem subst_lit (μ : Bn → Term Iri Lit Bn) (x : Lit) : subst μ (lit x) = lit x := rfl
@[simp] theorem subst_bnode (μ : Bn → Term Iri Lit Bn) (b : Bn) : subst μ (bnode b) = μ b := rfl

theorem subst_of_isName (μ : Bn → Term Iri Lit Bn) {x : Term Iri Lit Bn} (h : x.IsName) :
    subst μ x = x := by
  cases x <;> simp_all [IsName]

theorem subst_subst (ν μ : Bn → Term Iri Lit Bn) (x : Term Iri Lit Bn) :
    subst ν (subst μ x) = subst (fun b => subst ν (μ b)) x := by
  cases x <;> rfl
end Term

namespace Triple
variable {α β : Type}

def map (f : α → β) (t : Triple α) : Triple β := ⟨f t.s, f t.p, f t.o⟩

/-- The set of terms occurring in a triple. -/
def terms (t : Triple α) : Set α := {t.s, t.p, t.o}

@[simp] theorem map_id (t : Triple α) : map id t = t := rfl
@[simp] theorem map_id' (t : Triple α) : map (fun x => x) t = t := rfl

theorem map_map {γ : Type} (g : β → γ) (f : α → β) (t : Triple α) :
    map g (map f t) = map (g ∘ f) t := rfl

theorem map_congr {f g : α → β} {t : Triple α} (h : ∀ x ∈ t.terms, f x = g x) :
    map f t = map g t := by
  simp only [map, terms, Set.mem_insert_iff, Set.mem_singleton_iff] at *
  rw [h t.s (Or.inl rfl), h t.p (Or.inr (Or.inl rfl)), h t.o (Or.inr (Or.inr rfl))]

theorem map_eq_self {f : α → α} {t : Triple α} (h : ∀ x ∈ t.terms, f x = x) : map f t = t := by
  rw [map_congr h]; rfl

theorem mem_terms_map (f : α → β) (t : Triple α) {y : β} :
    y ∈ (map f t).terms ↔ ∃ x ∈ t.terms, f x = y := by
  simp only [map, terms, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h) <;> exact ⟨_, by simp, h.symm⟩
  · rintro ⟨x, (rfl | rfl | rfl), rfl⟩ <;> simp
end Triple

/-- An RDF graph (Definition 2), without the finiteness requirement. -/
abbrev Graph (Iri Lit Bn : Type) := Set (Triple (Term Iri Lit Bn))

namespace Graph
variable (G : Graph Iri Lit Bn)

/-- Pointwise application of a map on terms to a graph. -/
def mapT (f : Term Iri Lit Bn → Term Iri Lit Bn) (G : Graph Iri Lit Bn) : Graph Iri Lit Bn :=
  Triple.map f '' G

/-- `μ(G)`, the instance of `G` under `μ` (Definition 2). -/
def inst (μ : Bn → Term Iri Lit Bn) (G : Graph Iri Lit Bn) : Graph Iri Lit Bn :=
  mapT (Term.subst μ) G

/-- The blank nodes occurring in a graph. -/
def bnodes : Set Bn := {b | ∃ t ∈ G, Term.bnode b ∈ t.terms}

/-- The names occurring in a graph. -/
def names : Set (Term Iri Lit Bn) := {x | x.IsName ∧ ∃ t ∈ G, x ∈ t.terms}

/-- All terms occurring in a graph. -/
def terms : Set (Term Iri Lit Bn) := {x | ∃ t ∈ G, x ∈ t.terms}

/-- A graph is ground iff it contains no blank nodes. -/
def Ground : Prop := ∀ t ∈ G, ∀ x ∈ t.terms, Term.IsName x

/-- A graph is over `N` iff every term occurring in it lies in `N`. -/
def Over (N : Set (Term Iri Lit Bn)) : Prop := ∀ t ∈ G, ∀ x ∈ t.terms, x ∈ N

/-- Standard triples/graphs (Definition 1): no literal in subject position, an IRI in
predicate position. -/
def Standard : Prop :=
  ∀ t ∈ G, (∀ l, t.s ≠ Term.lit l) ∧ ∃ x, t.p = Term.iri x

theorem mapT_mapT (f g : Term Iri Lit Bn → Term Iri Lit Bn) :
    mapT f (mapT g G) = mapT (f ∘ g) G := by
  simp [mapT, Set.image_image, Triple.map_map]

theorem mapT_eq_self {f : Term Iri Lit Bn → Term Iri Lit Bn}
    (h : ∀ t ∈ G, ∀ x ∈ t.terms, f x = x) : mapT f G = G := by
  simp only [mapT]
  rw [Set.image_congr (fun t ht => Triple.map_eq_self (h t ht))]
  simp

theorem inst_inst (ν μ : Bn → Term Iri Lit Bn) :
    inst ν (inst μ G) = inst (fun b => Term.subst ν (μ b)) G := by
  simp only [inst, mapT_mapT]
  congr 1
  funext t
  simp [Term.subst_subst]

theorem inst_of_ground (μ : Bn → Term Iri Lit Bn) (h : G.Ground) : inst μ G = G :=
  mapT_eq_self G fun t ht x hx => Term.subst_of_isName μ (h t ht x hx)

theorem inst_mono {G H : Graph Iri Lit Bn} (μ : Bn → Term Iri Lit Bn) (h : G ⊆ H) :
    inst μ G ⊆ inst μ H := Set.image_mono h

theorem mapT_mono {G H : Graph Iri Lit Bn} (f : Term Iri Lit Bn → Term Iri Lit Bn) (h : G ⊆ H) :
    mapT f G ⊆ mapT f H := Set.image_mono h

theorem terms_inst_subset (μ : Bn → Term Iri Lit Bn) :
    (inst μ G).terms ⊆ G.names ∪ (μ '' G.bnodes) := by
  rintro x ⟨t', ⟨t, ht, rfl⟩, hx⟩
  obtain ⟨y, hy, rfl⟩ := (Triple.mem_terms_map _ _).1 hx
  cases y with
  | bnode b => exact Or.inr ⟨b, ⟨t, ht, hy⟩, rfl⟩
  | iri a => exact Or.inl ⟨trivial, t, ht, hy⟩
  | lit a => exact Or.inl ⟨trivial, t, ht, hy⟩

theorem ground_of_over {N : Set (Term Iri Lit Bn)} (hN : ∀ x ∈ N, Term.IsName x)
    (h : G.Over N) : G.Ground := fun t ht x hx => hN x (h t ht x hx)

theorem over_mono {N N' : Set (Term Iri Lit Bn)} (h : N ⊆ N') (hG : G.Over N) : G.Over N' :=
  fun t ht x hx => h (hG t ht x hx)

theorem over_of_subset {G H : Graph Iri Lit Bn} {N} (h : G ⊆ H) (hH : H.Over N) : G.Over N :=
  fun t ht => hH t (h ht)
end Graph

/-- Definition 3: `G` simply entails `H` iff some subgraph of `G` is an instance of `H`. -/
def SimpleEntails (G H : Graph Iri Lit Bn) : Prop := ∃ μ, Graph.inst μ H ⊆ G

/-- Simple entailment as stated under the standard syntax: the instance must itself be
standard. -/
def SimpleEntailsStd (G H : Graph Iri Lit Bn) : Prop :=
  ∃ μ, Graph.inst μ H ⊆ G ∧ (Graph.inst μ H).Standard

/-- Lemma 1 (Conservativity). -/
theorem simpleEntails_iff_std {G H : Graph Iri Lit Bn} (hG : G.Standard) :
    SimpleEntails G H ↔ SimpleEntailsStd G H := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨μ, hμ, fun t ht => hG t (hμ ht)⟩
  · rintro ⟨μ, hμ, -⟩
    exact ⟨μ, hμ⟩

/-! ### Entailment regimes (Definition 4) -/

/-- A rule `⟨A, c⟩`; `concl = none` is the false-concluding case `c = ⊥`. -/
structure Rule (Iri Lit Bn : Type) where
  prem  : Graph Iri Lit Bn
  concl : Option (Triple (Term Iri Lit Bn))

/-- Maps `ρ : I ∪ B ∪ L → I ∪ B ∪ L` fixing `L ∪ V` pointwise (Definition 4(2)). -/
def FixesLV (V : Set Iri) (ρ : Term Iri Lit Bn → Term Iri Lit Bn) : Prop :=
  (∀ l, ρ (Term.lit l) = Term.lit l) ∧ ∀ v ∈ V, ρ (Term.iri v) = Term.iri v

/-- Instance mappings, read as maps on terms, fix `L ∪ V`. -/
theorem fixesLV_subst (V : Set Iri) (μ : Bn → Term Iri Lit Bn) : FixesLV V (Term.subst μ) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

def Rule.map (ρ : Term Iri Lit Bn → Term Iri Lit Bn) (r : Rule Iri Lit Bn) : Rule Iri Lit Bn :=
  ⟨Graph.mapT ρ r.prem, r.concl.map (Triple.map ρ)⟩

/-- Definition 4: an entailment regime over `V`. -/
structure Regime (Iri Lit Bn : Type) (V : Set Iri) where
  rules : Set (Rule Iri Lit Bn)
  /-- (1) range restriction -/
  range : ∀ r ∈ rules, ∀ c, r.concl = some c →
    ∀ x ∈ c.terms, x ∈ r.prem.terms ∨ ∃ v ∈ V, x = Term.iri v
  /-- (2) uniformity -/
  uniform : ∀ ρ, FixesLV V ρ → ∀ r ∈ rules, r.map ρ ∈ rules

variable {V : Set Iri}

/-- The closure `cl_R(X)` as an inductive predicate on `L^RDF ∪ {⊥}`. -/
inductive Cl (R : Regime Iri Lit Bn V) (X : Graph Iri Lit Bn) :
    Option (Triple (Term Iri Lit Bn)) → Prop
  | base {t} : t ∈ X → Cl R X (some t)
  | step {r} : r ∈ R.rules → (∀ a ∈ r.prem, Cl R X (some a)) → Cl R X r.concl

namespace Regime
variable (R : Regime Iri Lit Bn V)

/-- `cl_R(X) \ {⊥}`. -/
def clPos (X : Graph Iri Lit Bn) : Graph Iri Lit Bn := {t | Cl R X (some t)}

/-- `X` is `R`-inconsistent iff `⊥ ∈ cl_R(X)`. -/
def Inconsistent (X : Graph Iri Lit Bn) : Prop := Cl R X none

/-- `G` `R`-entails `H`. -/
def Entails (G H : Graph Iri Lit Bn) : Prop :=
  R.Inconsistent G ∨ SimpleEntails (R.clPos G) H

theorem subset_clPos (X : Graph Iri Lit Bn) : X ⊆ R.clPos X := fun _ h => Cl.base h

theorem cl_mono {X Y : Graph Iri Lit Bn} (h : X ⊆ Y) {c} (hc : Cl R X c) : Cl R Y c := by
  induction hc with
  | base ht => exact Cl.base (h ht)
  | step hr _ ih => exact Cl.step hr ih

theorem clPos_mono {X Y : Graph Iri Lit Bn} (h : X ⊆ Y) : R.clPos X ⊆ R.clPos Y :=
  fun _ hc => R.cl_mono h hc

theorem inconsistent_mono {X Y : Graph Iri Lit Bn} (h : X ⊆ Y) (hX : R.Inconsistent X) :
    R.Inconsistent Y := R.cl_mono h hX

/-- Idempotence of the closure (used for closure under Cut). -/
theorem cl_clPos {X : Graph Iri Lit Bn} {c} (hc : Cl R (R.clPos X) c) : Cl R X c := by
  induction hc with
  | base ht => exact ht
  | step hr _ ih => exact Cl.step hr ih

/-- Lemma 6 (Uniformity of closure), first claim: `ρ(cl_R X) ⊆ cl_R(ρ X)`. -/
theorem cl_map {ρ} (hρ : FixesLV V ρ) {X : Graph Iri Lit Bn} {c} (hc : Cl R X c) :
    Cl R (Graph.mapT ρ X) (c.map (Triple.map ρ)) := by
  induction hc with
  | base ht => exact Cl.base ⟨_, ht, rfl⟩
  | step hr _ ih =>
    exact Cl.step (R.uniform ρ hρ _ hr) (by rintro a' ⟨a, ha, rfl⟩; exact ih a ha)

theorem clPos_map {ρ} (hρ : FixesLV V ρ) (X : Graph Iri Lit Bn) :
    Graph.mapT ρ (R.clPos X) ⊆ R.clPos (Graph.mapT ρ X) := by
  rintro _ ⟨t, ht, rfl⟩
  exact R.cl_map hρ ht

theorem inconsistent_map {ρ} (hρ : FixesLV V ρ) {X : Graph Iri Lit Bn} (h : R.Inconsistent X) :
    R.Inconsistent (Graph.mapT ρ X) := R.cl_map hρ h

/-- Lemma 6, second claim: every term of `cl_R(G) \ {⊥}` occurs in `G` or is in `V`. -/
theorem terms_clPos {G : Graph Iri Lit Bn} {c} (hc : Cl R G c) :
    ∀ t, c = some t → ∀ x ∈ t.terms, x ∈ G.terms ∨ ∃ v ∈ V, x = Term.iri v := by
  induction hc with
  | base ht =>
    intro t h x hx
    obtain rfl := Option.some.inj h
    exact Or.inl ⟨_, ht, hx⟩
  | @step r hr _ ih =>
    rintro t hct x hx
    rcases R.range r hr t hct x hx with ⟨a, ha, hxa⟩ | hv
    · exact ih a ha a rfl x hxa
    · exact Or.inr hv

theorem terms_clPos_subset (G : Graph Iri Lit Bn) :
    (R.clPos G).terms ⊆ G.terms ∪ ((fun v => Term.iri v) '' V) := by
  rintro x ⟨t, ht, hx⟩
  rcases R.terms_clPos ht t rfl x hx with h | ⟨v, hv, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, hv, rfl⟩

theorem bnodes_clPos_subset (G : Graph Iri Lit Bn) : (R.clPos G).bnodes ⊆ G.bnodes := by
  rintro b ⟨t, ht, hb⟩
  rcases R.terms_clPos ht t rfl _ hb with ⟨t', ht', hb'⟩ | ⟨v, _, h⟩
  · exact ⟨t', ht', hb'⟩
  · cases h
end Regime

/-- The empty regime (`R = ∅`), whose entailment is simple entailment. -/
def emptyRegime (Iri Lit Bn : Type) (V : Set Iri) : Regime Iri Lit Bn V where
  rules := ∅
  range := fun _ h => (Set.notMem_empty _ h).elim
  uniform := fun _ _ _ h => (Set.notMem_empty _ h).elim

theorem emptyRegime_cl {X : Graph Iri Lit Bn} {c} (h : Cl (emptyRegime Iri Lit Bn V) X c) :
    ∃ t ∈ X, c = some t := by
  induction h with
  | base ht => exact ⟨_, ht, rfl⟩
  | step hr _ _ => exact (Set.notMem_empty _ hr).elim

theorem emptyRegime_clPos (V : Set Iri) (X : Graph Iri Lit Bn) :
    (emptyRegime Iri Lit Bn V).clPos X = X := by
  ext t
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := emptyRegime_cl h
    exact Option.some.inj e ▸ ht'
  · exact fun h => Cl.base h

theorem emptyRegime_not_inconsistent (V : Set Iri) (X : Graph Iri Lit Bn) :
    ¬ (emptyRegime Iri Lit Bn V).Inconsistent X := by
  intro h
  obtain ⟨_, _, e⟩ := emptyRegime_cl h
  cases e

theorem emptyRegime_entails_iff (V : Set Iri) (G H : Graph Iri Lit Bn) :
    (emptyRegime Iri Lit Bn V).Entails G H ↔ SimpleEntails G H := by
  simp [Regime.Entails, emptyRegime_not_inconsistent, emptyRegime_clPos]

end ISRDF
