import ISRDF.Patterns
import ISRDF.Bridge

/-!
# Lost incoherence against cumulative relations

New declarations only; nothing earlier in the library is changed.

The claim checked.  In a cumulative relation (Kraus, Lehmann and Magidor 1990), from
`α |~ false` one derives `α ∧ β |~ false`, by Right Weakening and then Cautious
Monotonicity.  Property 1' of the notes (lost incoherence) gives a graph that is incoherent
and stops being so when a triple is added.  So a relation with lost incoherence cannot have
both rules.

* **Part A** is the derivation, in a form with no logic in it, and its two instances: the
  one for formulas, which is the cited lemma, and the one for sets of sentences, where `⊥`
  is the empty succedent.
* **Part B** applies it to the base of any `ConsBase`, with or without explosion, and says
  which of the two rules fails in each.
* **Part C** is the library's own example of lost incoherence (`Shapes.typeBase`).
-/

set_option autoImplicit false

namespace ISRDF
namespace NotCumulative

/-! ## Part A: the derivation -/

/-- **The derivation, with no logic in it.** `rel a c`: from premises `a`, conclude `c`.
`add a b`: the premises `a` with the conclusion `b` added.  If whatever concludes `bot`
concludes everything (`hRW`), and a conclusion may be added to the premises without loss
(`hCM`), then premises that conclude `bot` still do after any conclusion is added. -/
theorem bot_persists {P C : Type} (rel : P → C → Prop) (add : P → C → P) (bot : C)
    (hRW : ∀ a c, rel a bot → rel a c)
    (hCM : ∀ a b c, rel a b → rel a c → rel (add a b) c)
    {a : P} (h : rel a bot) (b : C) : rel (add a b) bot :=
  hCM a b bot (hRW a b h) h

/-- **The instance for formulas.** `ent` is the underlying entailment, `fls` a formula that
entails every formula, `nm` the nonmonotonic relation.  With Right Weakening and Cautious
Monotonicity: if `α |~ false` then `α ∧ β |~ false`.  Neither Cut, nor Reflexivity, nor Left
Logical Equivalence is used. -/
theorem klm_false_persists {F : Type} (and : F → F → F) (fls : F) (ent nm : F → F → Prop)
    (hfls : ∀ β, ent fls β)
    (hRW : ∀ α β γ, ent β γ → nm α β → nm α γ)
    (hCM : ∀ α β γ, nm α β → nm α γ → nm (and α β) γ)
    {α : F} (h : nm α fls) (β : F) : nm (and α β) fls :=
  bot_persists nm and fls (fun a c ha => hRW a fls c (hfls c) ha) hCM h β

section Sets
variable {T : Type}

/-- Right Weakening from the empty succedent: premises that imply `∅` imply every
sentence.  For a relation between sets this is explosion. -/
def RWBot (rel : Set T → Set T → Prop) : Prop := ∀ Γ t, rel Γ ∅ → rel Γ {t}

/-- Cautious Monotony: an implied sentence may be added to the premises without loss. -/
def CautiousMono (rel : Set T → Set T → Prop) : Prop :=
  ∀ Γ t Δ, rel Γ {t} → rel Γ Δ → rel (Γ ∪ {t}) Δ

/-- **The instance for sets of sentences.** With both rules, a set that implies `∅` still
does after any sentence is added. -/
theorem incoherence_persists {rel : Set T → Set T → Prop} (hRW : RWBot rel)
    (hCM : CautiousMono rel) {Γ : Set T} (h : rel Γ ∅) (t : T) : rel (Γ ∪ {t}) ∅ :=
  bot_persists (fun Γ (c : Option T) => rel Γ (c.elim ∅ (fun t => {t})))
    (fun Γ c => Γ ∪ c.elim ∅ (fun t => {t})) none
    (fun Γ c hb => by
      cases c with
      | none => exact hb
      | some t => exact hRW Γ t hb)
    (fun Γ b c hb hc => by
      cases b with
      | none =>
        show rel (Γ ∪ ∅) _
        rw [Set.union_empty]
        exact hc
      | some t => exact hCM Γ t _ hb hc)
    h (some t)

/-- And after any finite list of sentences is added. -/
theorem incoherence_persists_list {rel : Set T → Set T → Prop} (hRW : RWBot rel)
    (hCM : CautiousMono rel) {Γ : Set T} (h : rel Γ ∅) (l : List T) :
    rel (Γ ∪ {x | x ∈ l}) ∅ := by
  induction l with
  | nil =>
    have h0 : Γ ∪ {x | x ∈ ([] : List T)} = Γ := by
      ext x
      simp
    rw [h0]
    exact h
  | cons a l ih =>
    have h2 : Γ ∪ {x | x ∈ a :: l} = (Γ ∪ {x | x ∈ l}) ∪ {a} := by
      ext x
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, Set.mem_singleton_iff]
      tauto
    rw [h2]
    exact incoherence_persists hRW hCM ih a

/-- **No relation with lost incoherence has both rules.** -/
theorem not_both_of_lost_incoherence {rel : Set T → Set T → Prop} {Γ : Set T} {t : T}
    (h : rel Γ ∅) (h' : ¬ rel (Γ ∪ {t}) ∅) : ¬ (RWBot rel ∧ CautiousMono rel) :=
  fun ⟨hRW, hCM⟩ => h' (incoherence_persists hRW hCM h t)

end Sets

/-! ## Part B: the base of a `ConsBase`, with or without explosion -/

variable {Iri Lit Bn : Type} {V : Set Iri}

section Base
variable (C : ConsBase Iri Lit Bn V) (e : Prop) (N : Set (Term Iri Lit Bn))

/-- In either base, implying `∅` is incoherence. -/
theorem rel_empty_iff (Γ : Graph Iri Lit Bn) : (C.baseWith e N).rel Γ ∅ ↔ C.inc Γ := by
  show ((∅ ∩ C.cons Γ).Nonempty ∨ (C.inc Γ ∧ (e ∨ (∅ : Graph Iri Lit Bn) = ∅))) ↔ C.inc Γ
  constructor
  · rintro (⟨t, ht, -⟩ | ⟨hi, -⟩)
    · exact (Set.notMem_empty _ ht).elim
    · exact hi
  · exact fun hi => Or.inr ⟨hi, Or.inr rfl⟩

/-- In the base without explosion, a single sentence is implied iff it is a consequence. -/
theorem rel_singleton_iff (Γ : Graph Iri Lit Bn) (t : Triple (Term Iri Lit Bn)) :
    (C.baseWith False N).rel Γ {t} ↔ t ∈ C.cons Γ := by
  show (({t} ∩ C.cons Γ).Nonempty ∨
    (C.inc Γ ∧ (False ∨ ({t} : Graph Iri Lit Bn) = ∅))) ↔ t ∈ C.cons Γ
  constructor
  · rintro (⟨u, hu, hc⟩ | ⟨-, hf | he⟩)
    · rw [Set.mem_singleton_iff.1 hu] at hc
      exact hc
    · exact hf.elim
    · exact (Set.singleton_ne_empty _ he).elim
  · exact fun h => Or.inl ⟨t, Set.mem_singleton _, h⟩

/-- **Lost incoherence rules out the two rules together, in either base.** If `Γ` is
incoherent and `Γ ∪ {t}` is not, the base does not have both Right Weakening from the empty
succedent and Cautious Monotony, whether or not it explodes. -/
theorem not_cumulative {Γ : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)}
    (h : C.inc Γ) (h' : ¬ C.inc (Γ ∪ {t})) :
    ¬ (RWBot (C.baseWith e N).rel ∧ CautiousMono (C.baseWith e N).rel) :=
  not_both_of_lost_incoherence ((rel_empty_iff C e N Γ).2 h)
    (fun hr => h' ((rel_empty_iff C e N _).1 hr))

/-- The base with explosion has Right Weakening from the empty succedent. -/
theorem explosion_rwBot : RWBot (C.baseWith True N).rel :=
  fun Γ _ h => Or.inr ⟨(rel_empty_iff C True N Γ).1 h, Or.inl trivial⟩

/-- **With explosion, lost incoherence is a failure of Cautious Monotony.** `Γ` implies `t`
(by explosion) and implies `∅`, and `Γ ∪ {t}` does not imply `∅`.  The sentence added is not
a default conclusion. -/
theorem explosion_cm_fails {Γ : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)}
    (h : C.inc Γ) (h' : ¬ C.inc (Γ ∪ {t})) :
    (C.baseWith True N).rel Γ {t} ∧ (C.baseWith True N).rel Γ ∅ ∧
      ¬ (C.baseWith True N).rel (Γ ∪ {t}) ∅ :=
  ⟨Or.inr ⟨h, Or.inl trivial⟩, (rel_empty_iff C True N Γ).2 h,
    fun hr => h' ((rel_empty_iff C True N _).1 hr)⟩

/-- **Without explosion, lost incoherence is a failure of one rule or the other.** If the
added `t` is not a consequence of `Γ`, Right Weakening from the empty succedent fails at
`Γ` and `t`.  If it is, Cautious Monotony fails there. -/
theorem no_explosion_dichotomy {Γ : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)}
    (h : C.inc Γ) (h' : ¬ C.inc (Γ ∪ {t})) :
    ((C.baseWith False N).rel Γ ∅ ∧ ¬ (C.baseWith False N).rel Γ {t}) ∨
      ((C.baseWith False N).rel Γ {t} ∧ (C.baseWith False N).rel Γ ∅ ∧
        ¬ (C.baseWith False N).rel (Γ ∪ {t}) ∅) := by
  have h0 : (C.baseWith False N).rel Γ ∅ := (rel_empty_iff C False N Γ).2 h
  by_cases ht : t ∈ C.cons Γ
  · exact Or.inr ⟨(rel_singleton_iff C N Γ t).2 ht, h0,
      fun hr => h' ((rel_empty_iff C False N _).1 hr)⟩
  · exact Or.inl ⟨h0, fun hr => ht ((rel_singleton_iff C N Γ t).1 hr)⟩

/-- **Coherent sets are not closed under subsets.** With lost incoherence, some coherent
set has an incoherent subset. -/
theorem coherent_not_subset_closed {Γ : Graph Iri Lit Bn} {t : Triple (Term Iri Lit Bn)}
    (h : C.inc Γ) (h' : ¬ C.inc (Γ ∪ {t})) :
    ¬ (∀ X Y : Graph Iri Lit Bn, X ⊆ Y → ¬ C.inc Y → ¬ C.inc X) :=
  fun hall => hall Γ (Γ ∪ {t}) Set.subset_union_left h' h

end Base

/-! ## Part C: the library's example of lost incoherence -/

section TypeBase
open Examples (tri tri_inj)
open Shapes
variable {p t : Iri} {Ts : Set Iri}

/-- The example: "the subject of `p` must have one of the types `Ts`", over the empty
regime.  It has no default conclusions, so its consequence set is the graph. -/
theorem typeBase_cons (hp : p ∈ V) (ht : t ∈ V) (hTs : Ts ⊆ V) (X : Graph Iri Lit Bn) :
    (typeBase hp ht hTs).cons X = X := by
  rw [emptyRegime_entriesBase_cons]
  apply Set.Subset.antisymm
  · rintro c (hc | ⟨g, ⟨e', he', θ, -, rfl⟩, -, hc⟩)
    · exact hc
    · rw [Set.mem_singleton_iff.1 he'] at hc
      cases hc
  · exact Set.subset_union_left

/-- **The example has neither pair of rules, with or without explosion.** -/
theorem typeBase_not_cumulative (hp : p ∈ V) (ht : t ∈ V) (hTs : Ts ⊆ V) (htp : t ≠ p)
    {T : Iri} (hT : T ∈ Ts) (a c : Term Iri Lit Bn) (e : Prop)
    (N : Set (Term Iri Lit Bn)) :
    ¬ (RWBot ((typeBase hp ht hTs).baseWith e N).rel ∧
        CautiousMono ((typeBase hp ht hTs).baseWith e N).rel) :=
  not_cumulative _ e N (type_incoherence_lost hp ht hTs htp hT a c).1
    (type_incoherence_lost hp ht hTs htp hT a c).2

/-- **With explosion the example fails Cautious Monotony.** The untyped `{a p c}` implies
`a t T` and implies `∅`; with `a t T` added it does not imply `∅`. -/
theorem typeBase_explosion_cm_fails (hp : p ∈ V) (ht : t ∈ V) (hTs : Ts ⊆ V) (htp : t ≠ p)
    {T : Iri} (hT : T ∈ Ts) (a c : Term Iri Lit Bn) (N : Set (Term Iri Lit Bn)) :
    ((typeBase hp ht hTs).baseWith True N).rel {tri a p c} {tri a t (Term.iri T)} ∧
      ((typeBase hp ht hTs).baseWith True N).rel {tri a p c} ∅ ∧
      ¬ ((typeBase hp ht hTs).baseWith True N).rel
        ({tri a p c} ∪ {tri a t (Term.iri T)}) ∅ :=
  explosion_cm_fails _ N (type_incoherence_lost hp ht hTs htp hT a c).1
    (type_incoherence_lost hp ht hTs htp hT a c).2

/-- **Without explosion the example fails Right Weakening from the empty succedent.**
`{a p c}` implies `∅` and does not imply `a t T`. -/
theorem typeBase_no_explosion_rw_fails (hp : p ∈ V) (ht : t ∈ V) (hTs : Ts ⊆ V)
    (htp : t ≠ p) {T : Iri} (hT : T ∈ Ts) (a c : Term Iri Lit Bn)
    (N : Set (Term Iri Lit Bn)) :
    ((typeBase hp ht hTs).baseWith False N).rel {tri a p c} ∅ ∧
      ¬ ((typeBase hp ht hTs).baseWith False N).rel {tri a p c} {tri a t (Term.iri T)} := by
  refine ⟨(rel_empty_iff _ False N _).2 (type_incoherence_lost hp ht hTs htp hT a c).1, ?_⟩
  rw [rel_singleton_iff, typeBase_cons]
  intro h
  exact htp (tri_inj.1 (Set.mem_singleton_iff.1 h)).2.1

/-- **Without explosion the example has Cautious Monotony.** Its consequence set is the
graph, so an implied sentence is already a premise.  Here non-explosion alone is what
separates the base from a cumulative relation. -/
theorem typeBase_no_explosion_cm_holds (hp : p ∈ V) (ht : t ∈ V) (hTs : Ts ⊆ V)
    (N : Set (Term Iri Lit Bn)) :
    CautiousMono ((typeBase hp ht hTs : ConsBase Iri Lit Bn V).baseWith False N).rel := by
  intro Γ u Δ hu hΔ
  rw [rel_singleton_iff, typeBase_cons] at hu
  have hΓ : Γ ∪ {u} = Γ := Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.2 hu)
  rw [hΓ]
  exact hΔ

end TypeBase

end NotCumulative
end ISRDF
