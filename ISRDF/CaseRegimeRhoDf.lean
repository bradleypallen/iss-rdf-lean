import ISRDF.RhoDf

/-!
# The regime of the case study against rules (3a) and (3b) of ρdf

New declarations only; nothing earlier in the library is changed.

`Shapes.caseRegime` (in `Patterns.lean`) is the closure regime of the Wikidata case study:
`sub` is transitive, and `ins` passes up `sub`.  `RhoDf.rule` (in `RhoDf.lean`) transcribes
the rules of Muñoz, Pérez and Gutierrez.  The two files were written separately, with
different variables and with the premises of the second rule in a different order.  This
file compares them.

* `caseRegime_rules`: with `ins` the keyword `type` and `sub` the keyword `sc`, the rules of
  `caseRegime` are exactly the ground instances of rules (3a) and (3b) as transcribed in
  `RhoDf.rule`.
* `cl_rho_of_cl_case`: so the closure under the case study's regime lies inside the closure
  under all of rules (2) to (7).
* `case_or_refl_of_cl_rho`: on a graph with no triple whose predicate is `sp`, `dom` or
  `range`, and with the five keywords distinct, the converse holds up to reflexive triples:
  a triple of the closure under rules (2) to (7) is in the closure under the case study's
  regime, or it is `a sp a` or `a sc a` for some `a`.
* `cl_rho_iff_cl_case`: so on such a graph the two closures have the same triples that are
  not of those two reflexive forms; `cl_rho_type_iff` and `cl_rho_sc_iff` are the cases of
  a `type` triple and of an `sc` triple between different terms.

What this does not check: that `RhoDf.rule` agrees with the paper's table; that the graph of
the case study has no triple with one of the three predicates; and anything about the
defaults.
-/

set_option autoImplicit false

namespace ISRDF
namespace RhoDf

variable {Iri Lit Bn : Type} {V : Set Iri}

open Shapes (Vr)

local macro "cmp_simp" : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw,
      Shapes.subTransRule, Shapes.instUpRule, Shapes.pt])

local macro "cmp_simp" "at" h:ident : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw,
      Shapes.subTransRule, Shapes.instUpRule, Shapes.pt] at $h:ident)

section Rules
variable (voc : Vocab Iri)

/-- The transitivity rule of the case study, at `θ`, is rule (3a) at the matching
substitution. -/
theorem subTrans_inst_eq (θ : Vr → Term Iri Lit Bn) :
    (Shapes.subTransRule voc.sc : PRule Vr Iri Lit).inst θ =
      (rule voc RuleId.r3a).inst
        (fun v => match v with | RV.A => θ Vr.X | RV.B => θ Vr.Y | _ => θ Vr.C) := by
  cmp_simp

/-- The rule of the case study that passes `ins` up `sub`, at `θ`, is rule (3b) at the
matching substitution.  The premises are in the other order; a set does not see that. -/
theorem instUp_inst_eq (θ : Vr → Term Iri Lit Bn) :
    (Shapes.instUpRule voc.ty voc.sc : PRule Vr Iri Lit).inst θ =
      (rule voc RuleId.r3b).inst
        (fun v => match v with | RV.A => θ Vr.Y | RV.B => θ Vr.C | _ => θ Vr.X) := by
  cmp_simp
  exact Set.pair_comm _ _

/-- Rule (3a) at `θ` is the transitivity rule of the case study at the matching
substitution. -/
theorem r3a_inst_eq (θ : RV → Term Iri Lit Bn) :
    (rule (Lit := Lit) voc RuleId.r3a).inst θ =
      (Shapes.subTransRule voc.sc : PRule Vr Iri Lit).inst
        (fun v => match v with | Vr.X => θ RV.A | Vr.Y => θ RV.B | _ => θ RV.C) := by
  cmp_simp

/-- Rule (3b) at `θ` is the second rule of the case study at the matching substitution. -/
theorem r3b_inst_eq (θ : RV → Term Iri Lit Bn) :
    (rule (Lit := Lit) voc RuleId.r3b).inst θ =
      (Shapes.instUpRule voc.ty voc.sc : PRule Vr Iri Lit).inst
        (fun v => match v with | Vr.X => θ RV.X | Vr.Y => θ RV.A | _ => θ RV.B) := by
  cmp_simp
  exact Set.pair_comm _ _

/-- **The rules of the case study's regime are the instances of rules (3a) and (3b).** -/
theorem caseRegime_rules (hins : voc.ty ∈ V) (hsub : voc.sc ∈ V) :
    (Shapes.caseRegime (Lit := Lit) (Bn := Bn) hins hsub).rules =
      {g | ∃ θ : RV → Term Iri Lit Bn,
        g = (rule voc RuleId.r3a).inst θ ∨ g = (rule voc RuleId.r3b).inst θ} := by
  ext g
  constructor
  · rintro ⟨r, hr, θ, rfl⟩
    rcases Set.mem_insert_iff.1 hr with h | h
    · subst h
      exact ⟨_, Or.inl (subTrans_inst_eq voc θ)⟩
    · have h' := Set.mem_singleton_iff.1 h
      subst h'
      exact ⟨_, Or.inr (instUp_inst_eq voc θ)⟩
  · rintro ⟨θ, rfl | rfl⟩
    · exact ⟨_, Set.mem_insert _ _, _, r3a_inst_eq voc θ⟩
    · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_singleton _), _, r3b_inst_eq voc θ⟩

end Rules

/-- A regime with fewer rules has a smaller closure. -/
theorem cl_mono_rules {R R' : Regime Iri Lit Bn V} (h : R.rules ⊆ R'.rules)
    {X : Graph Iri Lit Bn} {c : Option (Triple (Term Iri Lit Bn))} (hc : Cl R X c) :
    Cl R' X c := by
  induction hc with
  | base ht => exact Cl.base ht
  | step hr _ ih => exact Cl.step (h hr) ih

section Closures
variable {voc : Vocab Iri} (hV : voc.In V) {X : Graph Iri Lit Bn}

/-- The case study's regime, with `ins` and `sub` the keywords `type` and `sc`. -/
abbrev caseOf (voc : Vocab Iri) (hV : voc.In V) : Regime Iri Lit Bn V :=
  Shapes.caseRegime (hV Kw.ty) (hV Kw.sc)

/-- The closure under the case study's regime lies inside the closure under rules (2) to
(7). -/
theorem cl_rho_of_cl_case {c : Option (Triple (Term Iri Lit Bn))}
    (hc : Cl (caseOf voc hV) X c) : Cl (rhoRegime voc hV) X c := by
  refine cl_mono_rules ?_ hc
  intro g hg
  rw [show (caseOf (Lit := Lit) (Bn := Bn) voc hV).rules = _ from
    caseRegime_rules voc (hV Kw.ty) (hV Kw.sc)] at hg
  obtain ⟨θ, rfl | rfl⟩ := hg
  · exact ⟨_, ⟨RuleId.r3a, rfl⟩, θ, rfl⟩
  · exact ⟨_, ⟨RuleId.r3b, rfl⟩, θ, rfl⟩

/-- Rule (3a) in the closure of the case study's regime. -/
theorem c3a {a b c : Term Iri Lit Bn}
    (h1 : Cl (caseOf voc hV) X (some ⟨a, Term.iri voc.sc, b⟩))
    (h2 : Cl (caseOf voc hV) X (some ⟨b, Term.iri voc.sc, c⟩)) :
    Cl (caseOf voc hV) X (some ⟨a, Term.iri voc.sc, c⟩) := by
  have hr : (rule (Lit := Lit) voc RuleId.r3a).inst
      (fun v => match v with | RV.A => a | RV.B => b | _ => c) ∈
      (caseOf (Bn := Bn) voc hV).rules := by
    rw [show (caseOf (Lit := Lit) (Bn := Bn) voc hV).rules = _ from
      caseRegime_rules voc (hV Kw.ty) (hV Kw.sc)]
    exact ⟨_, Or.inl rfl⟩
  have h := Cl.step (X := X) hr (by
    intro t ht
    cmp_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2])
  exact h

/-- Rule (3b) in the closure of the case study's regime. -/
theorem c3b {a b x : Term Iri Lit Bn}
    (h1 : Cl (caseOf voc hV) X (some ⟨a, Term.iri voc.sc, b⟩))
    (h2 : Cl (caseOf voc hV) X (some ⟨x, Term.iri voc.ty, a⟩)) :
    Cl (caseOf voc hV) X (some ⟨x, Term.iri voc.ty, b⟩) := by
  have hr : (rule (Lit := Lit) voc RuleId.r3b).inst
      (fun v => match v with | RV.A => a | RV.B => b | _ => x) ∈
      (caseOf (Bn := Bn) voc hV).rules := by
    rw [show (caseOf (Lit := Lit) (Bn := Bn) voc hV).rules = _ from
      caseRegime_rules voc (hV Kw.ty) (hV Kw.sc)]
    exact ⟨_, Or.inr rfl⟩
  have h := Cl.step (X := X) hr (by
    intro t ht
    cmp_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2])
  exact h

end Closures

section Conservative
variable {voc : Vocab Iri}

/-- The graph has no triple whose predicate is `sp`, `dom` or `range`. -/
def NoSchemaPred (voc : Vocab Iri) (X : Graph Iri Lit Bn) : Prop :=
  ∀ t ∈ X, t.p ≠ Term.iri voc.sp ∧ t.p ≠ Term.iri voc.dom ∧ t.p ≠ Term.iri voc.range

/-- The triple is `a k a` for some `a`. -/
def ReflAt (k : Iri) (t : Triple (Term Iri Lit Bn)) : Prop :=
  ∃ a : Term Iri Lit Bn, t = ⟨a, Term.iri k, a⟩

/-- What the induction keeps for each triple of the closure under rules (2) to (7): it is in
the closure under the case study's regime and its predicate is none of `sp`, `dom`, `range`;
or it is `a sp a`; or it is `a sc a`. -/
def CInv (voc : Vocab Iri) (hV : voc.In V) (X : Graph Iri Lit Bn)
    (t : Triple (Term Iri Lit Bn)) : Prop :=
  (Cl (caseOf voc hV) X (some t) ∧ t.p ≠ Term.iri voc.sp ∧ t.p ≠ Term.iri voc.dom ∧
      t.p ≠ Term.iri voc.range) ∨
    ReflAt voc.sp t ∨ ReflAt voc.sc t

variable (hV : voc.In V) {X : Graph Iri Lit Bn}

local macro "rho_simp" "at" h:ident : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw] at $h:ident)

local macro "rho_mem" : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw])

/-- A triple with predicate `sp` that satisfies the invariant is `a sp a`. -/
theorem cinv_sp (hd : Function.Injective voc.kw) {a b : Term Iri Lit Bn}
    (h : CInv voc hV X ⟨a, Term.iri voc.sp, b⟩) : a = b := by
  rcases h with ⟨-, h, -, -⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact (h rfl).elim
  · injection hc with h1 _ h3
    rw [h1, h3]
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.sp) (a₂ := Kw.sc) h2) (by simp)

/-- No triple with predicate `dom` satisfies the invariant. -/
theorem cinv_dom (hd : Function.Injective voc.kw) {a b : Term Iri Lit Bn}
    (h : CInv voc hV X ⟨a, Term.iri voc.dom, b⟩) : False := by
  rcases h with ⟨-, -, h, -⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact h rfl
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.dom) (a₂ := Kw.sp) h2) (by simp)
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.dom) (a₂ := Kw.sc) h2) (by simp)

/-- No triple with predicate `range` satisfies the invariant. -/
theorem cinv_range (hd : Function.Injective voc.kw) {a b : Term Iri Lit Bn}
    (h : CInv voc hV X ⟨a, Term.iri voc.range, b⟩) : False := by
  rcases h with ⟨-, -, -, h⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact h rfl
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.range) (a₂ := Kw.sp) h2) (by simp)
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.range) (a₂ := Kw.sc) h2) (by simp)

/-- A triple with predicate `sc` that satisfies the invariant is in the closure of the case
study's regime, or it is `a sc a`. -/
theorem cinv_sc (hd : Function.Injective voc.kw) {a b : Term Iri Lit Bn}
    (h : CInv voc hV X ⟨a, Term.iri voc.sc, b⟩) :
    Cl (caseOf voc hV) X (some ⟨a, Term.iri voc.sc, b⟩) ∨ a = b := by
  rcases h with ⟨h, -⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl h
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.sc) (a₂ := Kw.sp) h2) (by simp)
  · injection hc with h1 _ h3
    exact Or.inr (by rw [h1, h3])

/-- A triple with predicate `type` that satisfies the invariant is in the closure of the
case study's regime. -/
theorem cinv_ty (hd : Function.Injective voc.kw) {a b : Term Iri Lit Bn}
    (h : CInv voc hV X ⟨a, Term.iri voc.ty, b⟩) :
    Cl (caseOf voc hV) X (some ⟨a, Term.iri voc.ty, b⟩) := by
  rcases h with ⟨h, -⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact h
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.ty) (a₂ := Kw.sp) h2) (by simp)
  · injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.ty) (a₂ := Kw.sc) h2) (by simp)

/-- The invariant for a triple of the case study's closure with predicate `sc` or `type`. -/
theorem cinv_of_case (hd : Function.Injective voc.kw) {a b : Term Iri Lit Bn} {k : Kw}
    (hk : k = Kw.sc ∨ k = Kw.ty)
    (h : Cl (caseOf voc hV) X (some ⟨a, Term.iri (voc.kw k), b⟩)) :
    CInv voc hV X ⟨a, Term.iri (voc.kw k), b⟩ := by
  refine Or.inl ⟨h, ?_, ?_, ?_⟩
  · intro h2
    injection h2 with h2
    have h3 : k = Kw.sp := hd (a₂ := Kw.sp) h2
    rcases hk with rfl | rfl <;> cases h3
  · intro h2
    injection h2 with h2
    have h3 : k = Kw.dom := hd (a₂ := Kw.dom) h2
    rcases hk with rfl | rfl <;> cases h3
  · intro h2
    injection h2 with h2
    have h3 : k = Kw.range := hd (a₂ := Kw.range) h2
    rcases hk with rfl | rfl <;> cases h3

/-- The invariant holds of every triple of the closure under rules (2) to (7), on a graph
with no triple whose predicate is `sp`, `dom` or `range`. -/
theorem cinv_of_cl_rho (hd : Function.Injective voc.kw) (hX : NoSchemaPred voc X) :
    ∀ c, Cl (rhoRegime voc hV) X c → ∀ t, c = some t → CInv voc hV X t := by
  intro c hc
  induction hc with
  | @base t ht =>
    intro t' h
    obtain rfl : t = t' := Option.some.inj h
    exact Or.inl ⟨Cl.base ht, hX t ht⟩
  | @step r hr _ ih =>
    intro t hc
    obtain ⟨_, ⟨i, rfl⟩, θ, rfl⟩ := hr
    have ih' : ∀ a ∈ ((rule voc i).inst θ).prem, CInv voc hV X a := fun a ha => ih a ha a rfl
    cases i with
    | r2a =>
      have h1 := cinv_sp hV hd (ih' ⟨θ RV.A, Term.iri voc.sp, θ RV.B⟩ (by rho_mem))
      have h2 := cinv_sp hV hd (ih' ⟨θ RV.B, Term.iri voc.sp, θ RV.C⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inl ⟨θ RV.A, by rw [← h2, ← h1]⟩)
    | r2b =>
      have h1 := cinv_sp hV hd (ih' ⟨θ RV.A, Term.iri voc.sp, θ RV.B⟩ (by rho_mem))
      have h2 := ih' ⟨θ RV.X, θ RV.A, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      rw [← h1]
      exact h2
    | r3a =>
      have h1 := ih' ⟨θ RV.A, Term.iri voc.sc, θ RV.B⟩ (by rho_mem)
      have h2 := ih' ⟨θ RV.B, Term.iri voc.sc, θ RV.C⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      rcases cinv_sc hV hd h1 with g1 | g1
      · rcases cinv_sc hV hd h2 with g2 | g2
        · exact cinv_of_case hV hd (k := Kw.sc) (Or.inl rfl) (c3a hV g1 g2)
        · rw [← g2]
          exact h1
      · rw [g1]
        exact h2
    | r3b =>
      have h1 := ih' ⟨θ RV.A, Term.iri voc.sc, θ RV.B⟩ (by rho_mem)
      have h2 := ih' ⟨θ RV.X, Term.iri voc.ty, θ RV.A⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      rcases cinv_sc hV hd h1 with g1 | g1
      · exact cinv_of_case hV hd (k := Kw.ty) (Or.inr rfl) (c3b hV g1 (cinv_ty hV hd h2))
      · rw [← g1]
        exact h2
    | r4a =>
      exact (cinv_dom hV hd (ih' ⟨θ RV.A, Term.iri voc.dom, θ RV.B⟩ (by rho_mem))).elim
    | r4b =>
      exact (cinv_range hV hd (ih' ⟨θ RV.A, Term.iri voc.range, θ RV.B⟩ (by rho_mem))).elim
    | r5a =>
      exact (cinv_dom hV hd (ih' ⟨θ RV.A, Term.iri voc.dom, θ RV.B⟩ (by rho_mem))).elim
    | r5b =>
      exact (cinv_range hV hd (ih' ⟨θ RV.A, Term.iri voc.range, θ RV.B⟩ (by rho_mem))).elim
    | r6a =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inl ⟨θ RV.A, rfl⟩)
    | r6b1 =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inl ⟨θ RV.A, rfl⟩)
    | r6b2 =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inl ⟨θ RV.B, rfl⟩)
    | r6c p =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inl ⟨Term.iri (voc.kw p), rfl⟩)
    | r6dDom =>
      exact (cinv_dom hV hd (ih' ⟨θ RV.A, Term.iri voc.dom, θ RV.X⟩ (by rho_mem))).elim
    | r6dRange =>
      exact (cinv_range hV hd (ih' ⟨θ RV.A, Term.iri voc.range, θ RV.X⟩ (by rho_mem))).elim
    | r7a1 =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inr ⟨θ RV.A, rfl⟩)
    | r7a2 =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inr ⟨θ RV.B, rfl⟩)
    | r7bDom =>
      exact (cinv_dom hV hd (ih' ⟨θ RV.X, Term.iri voc.dom, θ RV.A⟩ (by rho_mem))).elim
    | r7bRange =>
      exact (cinv_range hV hd (ih' ⟨θ RV.X, Term.iri voc.range, θ RV.A⟩ (by rho_mem))).elim
    | r7bTy =>
      rho_simp at hc
      subst hc
      exact Or.inr (Or.inr ⟨θ RV.A, rfl⟩)

/-- **On a graph with no `sp`, `dom` or `range` triple, rules (2) to (7) add only reflexive
triples to what the case study's regime derives.** -/
theorem case_or_refl_of_cl_rho (hd : Function.Injective voc.kw) (hX : NoSchemaPred voc X)
    {t : Triple (Term Iri Lit Bn)} (h : Cl (rhoRegime voc hV) X (some t)) :
    Cl (caseOf voc hV) X (some t) ∨ ReflAt voc.sp t ∨ ReflAt voc.sc t := by
  rcases cinv_of_cl_rho hV hd hX _ h t rfl with ⟨h1, -⟩ | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- The two closures have the same triples that are not `a sp a` or `a sc a`. -/
theorem cl_rho_iff_cl_case (hd : Function.Injective voc.kw) (hX : NoSchemaPred voc X)
    {t : Triple (Term Iri Lit Bn)} (h1 : ¬ ReflAt voc.sp t) (h2 : ¬ ReflAt voc.sc t) :
    Cl (rhoRegime voc hV) X (some t) ↔ Cl (caseOf voc hV) X (some t) := by
  constructor
  · intro h
    rcases case_or_refl_of_cl_rho hV hd hX h with g | g | g
    · exact g
    · exact (h1 g).elim
    · exact (h2 g).elim
  · exact cl_rho_of_cl_case hV

/-- The two closures have the same `type` triples. -/
theorem cl_rho_type_iff (hd : Function.Injective voc.kw) (hX : NoSchemaPred voc X)
    (x c : Term Iri Lit Bn) :
    Cl (rhoRegime voc hV) X (some ⟨x, Term.iri voc.ty, c⟩) ↔
      Cl (caseOf voc hV) X (some ⟨x, Term.iri voc.ty, c⟩) := by
  refine cl_rho_iff_cl_case hV hd hX ?_ ?_
  · rintro ⟨a, ha⟩
    injection ha with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.ty) (a₂ := Kw.sp) h2) (by simp)
  · rintro ⟨a, ha⟩
    injection ha with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.ty) (a₂ := Kw.sc) h2) (by simp)

/-- The two closures have the same `sc` triples between different terms. -/
theorem cl_rho_sc_iff (hd : Function.Injective voc.kw) (hX : NoSchemaPred voc X)
    {a b : Term Iri Lit Bn} (hab : a ≠ b) :
    Cl (rhoRegime voc hV) X (some ⟨a, Term.iri voc.sc, b⟩) ↔
      Cl (caseOf voc hV) X (some ⟨a, Term.iri voc.sc, b⟩) := by
  refine cl_rho_iff_cl_case hV hd hX ?_ ?_
  · rintro ⟨c, hc⟩
    injection hc with _ h2 _
    injection h2 with h2
    exact absurd (hd (a₁ := Kw.sc) (a₂ := Kw.sp) h2) (by simp)
  · rintro ⟨c, hc⟩
    injection hc with h1 _ h3
    exact hab (by rw [h1, h3])

end Conservative

end RhoDf
end ISRDF
