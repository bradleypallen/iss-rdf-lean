import ISRDF.Patterns

/-!
# The standard patterns of nonmonotonic reasoning, against the entries base

New declarations only; nothing earlier in the library is changed.  The patterns are those
listed in Pelletier and Asher, "Generics and Defaults" (1997), section 3.1.

* **Part A** holds for every regime `R` and every set of entries `E`.
* **Part B** is a small family of entry sets over the empty regime ("class defaults":
  from `x type A` conclude `x type B` unless `x type T` for a listed `T`; and clashes:
  `x type A` and `x type B` give `⊥`), with `Cons` and incoherence computed for it.
* **Part C** works each pattern as a closed instance of Part B, with IRIs in `ℕ`.
-/

set_option autoImplicit false

namespace ISRDF
namespace StandardPatterns

open Examples (tri tri_inj)

variable {Iri Lit Bn : Type} {V : Set Iri}

/-! ## Part A: for every regime and every set of entries -/

section General
variable (R : Regime Iri Lit Bn V) (E : Entries Iri Lit Bn V)

/-- **Defeasible modus ponens.** The conclusion of an entry that applies at `cl_R(X)` is a
consequence of `X`. -/
theorem dmp {X : Graph Iri Lit Bn} {e : Entry Iri Lit Bn} (he : e ∈ E.entries)
    (ha : e.Applies (R.clPos X)) {c : Triple (Term Iri Lit Bn)} (hc : e.concl = some c) :
    c ∈ (R.entriesBase E).cons X := by
  rw [Regime.entriesBase_cons]
  exact R.subset_clPos _ (Or.inr ⟨e, he, ha, hc⟩)

/-- **A default conclusion is withdrawn only by a listed defeater.** If the entry applies
at `cl_R(X)` and no defeater of it is contained in `cl_R(Y)` for a larger `Y`, its
conclusion is still a consequence of `Y`, whatever else `Y` holds. -/
theorem persists {X Y : Graph Iri Lit Bn} (hXY : X ⊆ Y) {e : Entry Iri Lit Bn}
    (he : e ∈ E.entries) (ha : e.Applies (R.clPos X))
    (hd : ∀ D ∈ e.defeaters, ¬ D ⊆ R.clPos Y) {c : Triple (Term Iri Lit Bn)}
    (hc : e.concl = some c) : c ∈ (R.entriesBase E).cons Y :=
  dmp R E he ⟨Set.Subset.trans ha.1 (R.clPos_mono hXY), hd⟩ hc

/-- An entry with no defeaters is never defeated: its conclusion survives every extension
of the premises. -/
theorem persists_of_no_defeaters {X Y : Graph Iri Lit Bn} (hXY : X ⊆ Y)
    {e : Entry Iri Lit Bn} (he : e ∈ E.entries) (ha : e.Applies (R.clPos X))
    (h0 : e.defeaters = ∅) {c : Triple (Term Iri Lit Bn)} (hc : e.concl = some c) :
    c ∈ (R.entriesBase E).cons Y :=
  persists R E hXY he ha (fun D hD => by rw [h0] at hD; exact (Set.notMem_empty _ hD).elim) hc

/-- A listed defeater in the closure blocks the entry. -/
theorem not_applies_of_defeater {K : Graph Iri Lit Bn} {e : Entry Iri Lit Bn}
    {D : Graph Iri Lit Bn} (hD : D ∈ e.defeaters) (hsub : D ⊆ K) : ¬ e.Applies K :=
  fun ha => ha.2 D hD hsub

/-- **The consequence set is closed under the regime** (the second closure). -/
theorem cons_closed (X : Graph Iri Lit Bn) :
    R.clPos ((R.entriesBase E).cons X) = (R.entriesBase E).cons X :=
  Set.Subset.antisymm (fun _ ht => R.cl_clPos ht) (R.subset_clPos _)

/-- **Weakening of a default conclusion along the regime.** A rule of `R` whose premises
are consequences of `X`, default conclusions included, gives a consequence of `X`. -/
theorem cons_rule {X : Graph Iri Lit Bn} {r : Rule Iri Lit Bn} (hr : r ∈ R.rules)
    (hp : r.prem ⊆ (R.entriesBase E).cons X) {d : Triple (Term Iri Lit Bn)}
    (hd : r.concl = some d) : d ∈ (R.entriesBase E).cons X := by
  rw [← cons_closed R E X]
  have h : Cl R ((R.entriesBase E).cons X) r.concl :=
    Cl.step hr (fun a ha => Cl.base (hp ha))
  rw [hd] at h
  exact h

/-- **Independence, in the base without explosion.** Whether a triple is implied does not
depend on whether the premises are incoherent. -/
theorem rel_singleton_iff (N : Set (Term Iri Lit Bn)) {X : Graph Iri Lit Bn}
    {t : Triple (Term Iri Lit Bn)} :
    ((R.entriesBase E).base N).rel X {t} ↔ t ∈ (R.entriesBase E).cons X :=
  Examples.rel_singleton _ N

end General

/-! ## Part B: class defaults and clashes over the empty regime -/

/-- The pattern `X type C`, in one variable. -/
abbrev cp (ty C : Iri) : PTriple Unit Iri Lit := ⟨PTerm.var (), PTerm.iri ty, PTerm.iri C⟩

/-- The triple `x type C`. -/
abbrev isA (x : Term Iri Lit Bn) (ty C : Iri) : Triple (Term Iri Lit Bn) :=
  tri x ty (Term.iri C)

/-- From `X type A` conclude `X type B`, unless `X type T` for some `T` in `Ts`. -/
def dflt (ty A B : Iri) (Ts : Set Iri) : PEntry Unit Iri Lit Bn where
  prem := {cp ty A}
  concl := some (cp ty B)
  defeaters := {D | ∃ T ∈ Ts, D = {cp ty T}}
  guard := fun _ => True

/-- `X type A` and `X type B` give `⊥`. -/
def clash (ty A B : Iri) : PEntry Unit Iri Lit Bn where
  prem := {cp ty A, cp ty B}
  concl := none
  defeaters := ∅
  guard := fun _ => True

theorem unit_mem_vars (ty A : Iri) :
    () ∈ PGraph.vars ({cp ty A} : PGraph Unit Iri Lit) :=
  ⟨cp ty A, Set.mem_singleton _, by simp [Triple.terms]⟩

theorem dflt_wf {ty A B : Iri} {Ts : Set Iri} (hty : ty ∈ V) (hA : A ∈ V) (hB : B ∈ V)
    (hTs : Ts ⊆ V) : (dflt ty A B Ts : PEntry Unit Iri Lit Bn).WF V where
  prem := PGraph.over_singleton (PGraph.const_terms trivial hty hA)
  concl := by
    intro c hc
    rw [← Option.some.inj hc]
    intro z hz
    simp only [Triple.terms, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl ⟨cp ty A, Set.mem_singleton _, by simp [Triple.terms]⟩
    · exact Or.inr ⟨ty, hty, rfl⟩
    · exact Or.inr ⟨B, hB, rfl⟩
  defeaters := by
    rintro _ ⟨T, hT, rfl⟩
    exact PGraph.over_singleton (PGraph.const_terms trivial hty (hTs hT))
  guard := (guardInvariant_true _).proj

theorem clash_wf {ty A B : Iri} (hty : ty ∈ V) (hA : A ∈ V) (hB : B ∈ V) :
    (clash ty A B : PEntry Unit Iri Lit Bn).WF V where
  prem := PGraph.over_insert (PGraph.const_terms trivial hty hA)
    (PGraph.over_singleton (PGraph.const_terms trivial hty hB))
  concl := by
    intro c hc
    cases hc
  defeaters := fun D hD => (Set.notMem_empty _ hD).elim
  guard := (guardInvariant_true _).proj

/-- A set of class defaults `(A, B, Ts)` and clashes `(A, B)` over one typing predicate. -/
structure Spec (Iri : Type) where
  ty : Iri
  defaults : Set (Iri × Iri × Set Iri)
  clashes : Set (Iri × Iri)

/-- The constants of a `Spec` lie in `V`. -/
structure Spec.Over (V : Set Iri) (S : Spec Iri) : Prop where
  ty : S.ty ∈ V
  defaults : ∀ d ∈ S.defaults, d.1 ∈ V ∧ d.2.1 ∈ V ∧ d.2.2 ⊆ V
  clashes : ∀ c ∈ S.clashes, c.1 ∈ V ∧ c.2 ∈ V

/-- The pattern entries of a `Spec`. -/
def Spec.pentries (Lit Bn : Type) (S : Spec Iri) : Set (PEntry Unit Iri Lit Bn) :=
  {e | (∃ d ∈ S.defaults, e = dflt S.ty d.1 d.2.1 d.2.2) ∨
       (∃ c ∈ S.clashes, e = clash S.ty c.1 c.2)}

theorem Spec.pentries_wf (S : Spec Iri) (h : S.Over V) :
    ∀ e ∈ S.pentries Lit Bn, e.WF V := by
  rintro e (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
  · exact dflt_wf h.ty (h.defaults d hd).1 (h.defaults d hd).2.1 (h.defaults d hd).2.2
  · exact clash_wf h.ty (h.clashes c hc).1 (h.clashes c hc).2

/-- The entries of a `Spec`: range-restricted and closed under renamings, by
`patternEntries`. -/
def Spec.entries (S : Spec Iri) (h : S.Over V) : Entries Iri Lit Bn V :=
  patternEntries (S.pentries Lit Bn) (S.pentries_wf h)

/-- The base of a `Spec` over the empty regime. -/
abbrev Spec.base (S : Spec Iri) (h : S.Over V) : ConsBase Iri Lit Bn V :=
  (emptyRegime Iri Lit Bn V).entriesBase (S.entries h)

/-- `Cons` for a `Spec`: the graph, with the conclusion of each default whose premise is in
the graph and none of whose listed defeaters is. -/
theorem mem_cons_iff (S : Spec Iri) (h : S.Over V) {K : Graph Iri Lit Bn}
    {t : Triple (Term Iri Lit Bn)} :
    t ∈ (S.base h).cons K ↔
      t ∈ K ∨ ∃ d ∈ S.defaults, ∃ x : Term Iri Lit Bn, isA x S.ty d.1 ∈ K ∧
        (∀ T ∈ d.2.2, isA x S.ty T ∉ K) ∧ t = isA x S.ty d.2.1 := by
  rw [emptyRegime_entriesBase_cons]
  constructor
  · rintro (ht | ⟨g, ⟨e, he, θ, -, rfl⟩, ha, hc⟩)
    · exact Or.inl ht
    · rcases he with ⟨d, hd, rfl⟩ | ⟨c, -, rfl⟩
      · refine Or.inr ⟨d, hd, θ (), ha.1 ⟨cp S.ty d.1, Set.mem_singleton _, rfl⟩, ?_,
          (Option.some.inj hc).symm⟩
        intro T hT hmem
        refine ha.2 _ ⟨{cp S.ty T}, ⟨T, hT, rfl⟩, θ, fun _ _ => rfl, rfl⟩ ?_
        rintro _ ⟨t', ht', rfl⟩
        rw [Set.mem_singleton_iff.1 ht']
        exact hmem
      · cases hc
  · rintro (ht | ⟨d, hd, x, hprem, hdef, rfl⟩)
    · exact Or.inl ht
    · refine Or.inr ⟨(dflt S.ty d.1 d.2.1 d.2.2).inst (fun _ => x),
        ⟨_, Or.inl ⟨d, hd, rfl⟩, _, trivial, rfl⟩, ⟨?_, ?_⟩, rfl⟩
      · rintro _ ⟨t', ht', rfl⟩
        rw [Set.mem_singleton_iff.1 ht']
        exact hprem
      · rintro _ ⟨D, ⟨T, hT, rfl⟩, η, hη, rfl⟩ hsub
        have h1 : isA (η ()) S.ty T ∈ K := hsub ⟨cp S.ty T, Set.mem_singleton _, rfl⟩
        rw [hη () (unit_mem_vars S.ty d.1)] at h1
        exact hdef T hT h1

/-- Incoherence for a `Spec`: some clash has both of its triples in the graph. -/
theorem inc_iff (S : Spec Iri) (h : S.Over V) {K : Graph Iri Lit Bn} :
    (S.base h).inc K ↔
      ∃ c ∈ S.clashes, ∃ x : Term Iri Lit Bn, isA x S.ty c.1 ∈ K ∧ isA x S.ty c.2 ∈ K := by
  rw [emptyRegime_entriesBase_inc]
  constructor
  · rintro ⟨g, ⟨e, he, θ, -, rfl⟩, ha, hc⟩
    rcases he with ⟨d, -, rfl⟩ | ⟨c, hc', rfl⟩
    · cases hc
    · exact ⟨c, hc', θ (), ha.1 ⟨cp S.ty c.1, Set.mem_insert _ _, rfl⟩,
        ha.1 ⟨cp S.ty c.2, Set.mem_insert_of_mem _ (Set.mem_singleton _), rfl⟩⟩
  · rintro ⟨c, hc, x, h1, h2⟩
    refine ⟨(clash S.ty c.1 c.2).inst (fun _ => x),
      ⟨_, Or.inr ⟨c, hc, rfl⟩, _, trivial, rfl⟩, ⟨?_, ?_⟩, rfl⟩
    · rintro _ ⟨t', ht', rfl⟩
      rcases Set.mem_insert_iff.1 ht' with ht' | ht'
      · rw [ht']
        exact h1
      · rw [Set.mem_singleton_iff.1 ht']
        exact h2
    · rintro _ ⟨D, hD, -⟩
      exact (Set.notMem_empty _ hD).elim

/-! ## Part C: the patterns as closed instances

IRIs are natural numbers.  The vocabulary `Voc` is the IRIs below 50: the typing predicate
`0` and the classes.  Individuals are IRIs from 100 up, outside the vocabulary. -/

section Closed
variable {Lit Bn : Type}

/-- The vocabulary of the closed instances. -/
abbrev Voc : Set ℕ := {n | n < 50}

local notation "ty" => (0 : ℕ)
local notation "bird" => (1 : ℕ)
local notation "flies" => (2 : ℕ)
local notation "nonflier" => (3 : ℕ)
local notation "penguin" => (4 : ℕ)
local notation "quaker" => (5 : ℕ)
local notation "republican" => (6 : ℕ)
local notation "pacifist" => (7 : ℕ)
local notation "hawk" => (8 : ℕ)
local notation "active" => (9 : ℕ)
local notation "dog" => (10 : ℕ)
local notation "hairy" => (11 : ℕ)
local notation "fourlegs" => (12 : ℕ)
local notation "threelegs" => (13 : ℕ)
local notation "barks" => (14 : ℕ)
local notation "adult" => (15 : ℕ)
local notation "employed" => (16 : ℕ)
local notation "unemployed" => (17 : ℕ)
local notation "student" => (18 : ℕ)
local notation "tweety" => (Term.iri 100 : Term ℕ Lit Bn)
local notation "nixon" => (Term.iri 101 : Term ℕ Lit Bn)
local notation "fido" => (Term.iri 102 : Term ℕ Lit Bn)
local notation "charlie" => (Term.iri 103 : Term ℕ Lit Bn)
local notation "sam" => (Term.iri 104 : Term ℕ Lit Bn)

/-! ### Defeasible modus ponens and its defeat -/

/-- Birds fly, with no listed defeater; flying and being a non-flier clash. -/
def S1 : Spec ℕ := ⟨ty, {(bird, flies, ∅)}, {(flies, nonflier)}⟩

theorem S1_over : S1.Over Voc := by constructor <;> simp [S1, Voc]

/-- **Defeasible modus ponens.** From "Tweety is a bird", Tweety flies. -/
theorem c1_dmp :
    isA tweety ty flies ∈ (S1.base S1_over).cons ({isA tweety ty bird} : Graph ℕ Lit Bn) := by
  simp only [mem_cons_iff]
  simp [S1]

/-- **The negation of the conclusion does not defeat it, unless listed.** Add "Tweety is a
non-flier".  The conclusion that Tweety flies is still drawn; the graph is not incoherent;
its consequence set is. -/
theorem c2_conflict_located :
    isA tweety ty flies ∈ (S1.base S1_over).cons
        ({isA tweety ty bird, isA tweety ty nonflier} : Graph ℕ Lit Bn) ∧
      ¬ (S1.base S1_over).inc ({isA tweety ty bird, isA tweety ty nonflier} : Graph ℕ Lit Bn) ∧
      (S1.base S1_over).inc ((S1.base S1_over).cons
        ({isA tweety ty bird, isA tweety ty nonflier} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S1]

/-- Birds fly, unless a non-flier: the same default with its defeater listed. -/
def S1' : Spec ℕ := ⟨ty, {(bird, flies, {nonflier})}, {(flies, nonflier)}⟩

theorem S1'_over : S1'.Over Voc := by constructor <;> simp [S1', Voc]

/-- **Defeat by a listed defeater.** With the defeater listed, the conclusion is not drawn,
and the consequence set is coherent. -/
theorem c2_listed_defeater :
    isA tweety ty flies ∈ (S1'.base S1'_over).cons ({isA tweety ty bird} : Graph ℕ Lit Bn) ∧
      isA tweety ty flies ∉ (S1'.base S1'_over).cons
        ({isA tweety ty bird, isA tweety ty nonflier} : Graph ℕ Lit Bn) ∧
      ¬ (S1'.base S1'_over).inc ((S1'.base S1'_over).cons
        ({isA tweety ty bird, isA tweety ty nonflier} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S1']

/-! ### The Nixon diamond and its extension -/

/-- Quakers are pacifists; Republicans are hawks; pacifist and hawk clash. -/
def S3 : Spec ℕ := ⟨ty, {(quaker, pacifist, ∅), (republican, hawk, ∅)}, {(pacifist, hawk)}⟩

theorem S3_over : S3.Over Voc := by constructor <;> simp [S3, Voc]

/-- **Nixon diamond.** Both conclusions are drawn.  The graph is not incoherent; its
consequence set is. -/
theorem c3_nixon :
    isA nixon ty pacifist ∈ (S3.base S3_over).cons
        ({isA nixon ty quaker, isA nixon ty republican} : Graph ℕ Lit Bn) ∧
      isA nixon ty hawk ∈ (S3.base S3_over).cons
        ({isA nixon ty quaker, isA nixon ty republican} : Graph ℕ Lit Bn) ∧
      ¬ (S3.base S3_over).inc ({isA nixon ty quaker, isA nixon ty republican} : Graph ℕ Lit Bn) ∧
      (S3.base S3_over).inc ((S3.base S3_over).cons
        ({isA nixon ty quaker, isA nixon ty republican} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S3]

/-- The Nixon diamond with two more defaults: pacifists are politically active, and so are
hawks. -/
def S4 : Spec ℕ :=
  ⟨ty, {(quaker, pacifist, ∅), (republican, hawk, ∅), (pacifist, active, ∅), (hawk, active, ∅)},
    {(pacifist, hawk)}⟩

theorem S4_over : S4.Over Voc := by constructor <;> simp [S4, Voc]

/-- **Extended Nixon diamond: defaults do not chain.** "Nixon is politically active" is not
a consequence, although it is a consequence of the consequence set. -/
theorem c4_no_chaining :
    isA nixon ty active ∉ (S4.base S4_over).cons
        ({isA nixon ty quaker, isA nixon ty republican} : Graph ℕ Lit Bn) ∧
      isA nixon ty active ∈ (S4.base S4_over).cons ((S4.base S4_over).cons
        ({isA nixon ty quaker, isA nixon ty republican} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff]
  simp [S4]

/-! ### The Penguin Principle -/

/-- Birds fly; penguins are non-fliers; neither default lists a defeater. -/
def S5 : Spec ℕ := ⟨ty, {(bird, flies, ∅), (penguin, nonflier, ∅)}, {(flies, nonflier)}⟩

theorem S5_over : S5.Over Voc := by constructor <;> simp [S5, Voc]

/-- **Penguin Principle, no specificity.** The strict fact that penguins are birds is put
into the graph by hand, as a regime would put it into the closure.  Both conclusions are
drawn, and the conflict is in the consequence set. -/
theorem c5_penguin_no_specificity :
    isA tweety ty flies ∈ (S5.base S5_over).cons
        ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn) ∧
      isA tweety ty nonflier ∈ (S5.base S5_over).cons
        ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn) ∧
      ¬ (S5.base S5_over).inc ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn) ∧
      (S5.base S5_over).inc ((S5.base S5_over).cons
        ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S5]

/-- Birds fly, unless penguins; penguins are non-fliers. -/
def S5' : Spec ℕ := ⟨ty, {(bird, flies, {penguin}), (penguin, nonflier, ∅)}, {(flies, nonflier)}⟩

theorem S5'_over : S5'.Over Voc := by constructor <;> simp [S5', Voc]

/-- **Penguin Principle, with the specific class listed as a defeater.** Tweety is a
non-flier, is not concluded to fly, and the consequence set is coherent. -/
theorem c5_penguin_listed :
    isA tweety ty nonflier ∈ (S5'.base S5'_over).cons
        ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn) ∧
      isA tweety ty flies ∉ (S5'.base S5'_over).cons
        ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn) ∧
      ¬ (S5'.base S5'_over).inc ((S5'.base S5'_over).cons
        ({isA tweety ty penguin, isA tweety ty bird} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S5']

/-- Adults are employed; students are unemployed; students are adults (a default, not a
strict fact); employed and unemployed clash.  No default lists a defeater. -/
def S5w : Spec ℕ :=
  ⟨ty, {(adult, employed, ∅), (student, unemployed, ∅), (student, adult, ∅)},
    {(employed, unemployed)}⟩

theorem S5w_over : S5w.Over Voc := by constructor <;> simp [S5w, Voc]

/-- **Weak Penguin Principle.** Sam is a student.  He is concluded unemployed and adult,
and is not concluded employed: "Sam is an adult" is a default conclusion, and the default
about adults does not see it.  The consequence set is coherent.  The specific default
prevails here because defaults do not chain, not because of specificity. -/
theorem c5_weak_penguin :
    isA sam ty unemployed ∈ (S5w.base S5w_over).cons ({isA sam ty student} : Graph ℕ Lit Bn) ∧
      isA sam ty adult ∈ (S5w.base S5w_over).cons ({isA sam ty student} : Graph ℕ Lit Bn) ∧
      isA sam ty employed ∉ (S5w.base S5w_over).cons ({isA sam ty student} : Graph ℕ Lit Bn) ∧
      ¬ (S5w.base S5w_over).inc ((S5w.base S5w_over).cons
        ({isA sam ty student} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S5w]

/-! ### Independence -/

/-- Dogs are hairy; dogs have four legs; four legs and three legs clash. -/
def S6 : Spec ℕ := ⟨ty, {(dog, hairy, ∅), (dog, fourlegs, ∅)}, {(fourlegs, threelegs)}⟩

theorem S6_over : S6.Over Voc := by constructor <;> simp [S6, Voc]

/-- **Pelletier and Asher's (27).** Fido is a three-legged dog.  He is concluded hairy.  He
is also concluded four-legged, and that conflict is in the consequence set. -/
theorem c6_fido :
    isA fido ty hairy ∈ (S6.base S6_over).cons
        ({isA fido ty dog, isA fido ty threelegs} : Graph ℕ Lit Bn) ∧
      isA fido ty fourlegs ∈ (S6.base S6_over).cons
        ({isA fido ty dog, isA fido ty threelegs} : Graph ℕ Lit Bn) ∧
      ¬ (S6.base S6_over).inc ({isA fido ty dog, isA fido ty threelegs} : Graph ℕ Lit Bn) ∧
      (S6.base S6_over).inc ((S6.base S6_over).cons
        ({isA fido ty dog, isA fido ty threelegs} : Graph ℕ Lit Bn)) := by
  simp only [mem_cons_iff, inc_iff]
  simp [S6]

/-- Birds fly; dogs bark; flying and being a non-flier clash. -/
def S7 : Spec ℕ := ⟨ty, {(bird, flies, ∅), (dog, barks, ∅)}, {(flies, nonflier)}⟩

theorem S7_over : S7.Over Voc := by constructor <;> simp [S7, Voc]

/-- **Pelletier and Asher's (28).** Tweety is a non-flying bird and Charlie is a dog.
Charlie barks. -/
theorem c7_charlie :
    isA charlie ty barks ∈ (S7.base S7_over).cons
      ({isA tweety ty bird, isA tweety ty nonflier, isA charlie ty dog} : Graph ℕ Lit Bn) := by
  simp only [mem_cons_iff]
  simp [S7]

/-- (28) on an incoherent graph: state also that Tweety flies.  The graph is incoherent,
and Charlie still barks, as a consequence and in the base without explosion. -/
theorem c7_charlie_incoherent (N : Set (Term ℕ Lit Bn)) :
    (S7.base S7_over).inc ({isA tweety ty bird, isA tweety ty nonflier, isA tweety ty flies,
        isA charlie ty dog} : Graph ℕ Lit Bn) ∧
      isA charlie ty barks ∈ (S7.base S7_over).cons ({isA tweety ty bird,
        isA tweety ty nonflier, isA tweety ty flies, isA charlie ty dog} : Graph ℕ Lit Bn) ∧
      ((S7.base S7_over).base N).rel ({isA tweety ty bird, isA tweety ty nonflier,
        isA tweety ty flies, isA charlie ty dog} : Graph ℕ Lit Bn) {isA charlie ty barks} := by
  rw [Examples.rel_singleton]
  simp only [mem_cons_iff, inc_iff]
  simp [S7]

end Closed

end StandardPatterns
end ISRDF
