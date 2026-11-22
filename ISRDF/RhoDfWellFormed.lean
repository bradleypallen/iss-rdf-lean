import ISRDF.RhoDf

/-!
# The ρdf rules: generalized instances against well-formed instances

New declarations only; nothing earlier in the library is changed.

Muñoz, Pérez and Gutierrez take an RDF triple to be an element of `UBL × U × UBL`: any term
as subject or object, a URI as predicate.  They instantiate a rule of their Table 1 only
where every resulting triple is such a triple.  `RhoDf.rhoRegime` takes every instance over
generalized triples, so its closure can contain triples whose predicate is a blank node or
a literal.  Rule (2b) produces them: from `a sp b` and `x a y` it gives `x b y`, whatever
`b` is.

This file shows that the difference does not matter for graphs whose predicates are IRIs.

* `WCl` is the closure of a graph under the instances of rules (2) to (7) in which every
  triple has an IRI as predicate: the paper's instances.
* `wcl_of_mem_clPos`: on a graph whose predicates are IRIs, every triple of the generalized
  closure that has an IRI as predicate is in `WCl`.  The proof keeps, for a triple `x b y`
  whose predicate `b` is not an IRI, an IRI `a` with `x a y` and `a sp b` in `WCl`; rules
  (5a), (5b) and (6b) of the paper are what make the induction go through.
* `mem_clPos_of_wcl`: the converse inclusion, which holds for every graph.
* `simpleEntails_clPos_iff_wcl`: so the two closures simply entail the same graphs whose
  predicates are IRIs.
* `rho_recovery_wellFormed`: Theorem 2 for the ρdf rules, stated with the paper's closure.

What this does not check: that `RhoDf.rule` agrees with the paper's table, and the paper's
theorems about RDFS entailment.
-/

set_option autoImplicit false

namespace ISRDF
namespace RhoDf

variable {Iri Lit Bn : Type} {V : Set Iri}

/-- The predicate of the triple is an IRI. -/
def IriPred (t : Triple (Term Iri Lit Bn)) : Prop := ∃ i : Iri, t.p = Term.iri i

/-- The closure of `X` under the instances of rules (2) to (7) all of whose triples have an
IRI as predicate. -/
inductive WCl (voc : Vocab Iri) (X : Graph Iri Lit Bn) : Triple (Term Iri Lit Bn) → Prop
  | base {t : Triple (Term Iri Lit Bn)} : t ∈ X → WCl voc X t
  | step (i : RuleId) (θ : RV → Term Iri Lit Bn) {c : Triple (Term Iri Lit Bn)} :
      (∀ a ∈ ((rule voc i).inst θ).prem, IriPred a) → IriPred c →
      ((rule voc i).inst θ).concl = some c →
      (∀ a ∈ ((rule voc i).inst θ).prem, WCl voc X a) → WCl voc X c

section WellFormedRules
variable {voc : Vocab Iri} {X : Graph Iri Lit Bn}

local macro "rho_simp" "at" h:ident : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw] at $h:ident)

/-! Each rule as a closure property of `WCl`, at the instances the proof below uses. -/

theorem w2a {a b c : Term Iri Lit Bn} (h1 : WCl voc X ⟨a, Term.iri voc.sp, b⟩)
    (h2 : WCl voc X ⟨b, Term.iri voc.sp, c⟩) : WCl voc X ⟨a, Term.iri voc.sp, c⟩ := by
  refine WCl.step RuleId.r2a (fun v => match v with | RV.A => a | RV.B => b | _ => c)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2]

theorem w2b {p q : Iri} {x y : Term Iri Lit Bn}
    (h1 : WCl voc X ⟨Term.iri p, Term.iri voc.sp, Term.iri q⟩)
    (h2 : WCl voc X ⟨x, Term.iri p, y⟩) : WCl voc X ⟨x, Term.iri q, y⟩ := by
  refine WCl.step RuleId.r2b
    (fun v => match v with | RV.A => Term.iri p | RV.B => Term.iri q | RV.X => x | _ => y)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2]

theorem w3a {a b c : Term Iri Lit Bn} (h1 : WCl voc X ⟨a, Term.iri voc.sc, b⟩)
    (h2 : WCl voc X ⟨b, Term.iri voc.sc, c⟩) : WCl voc X ⟨a, Term.iri voc.sc, c⟩ := by
  refine WCl.step RuleId.r3a (fun v => match v with | RV.A => a | RV.B => b | _ => c)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2]

theorem w3b {a b x : Term Iri Lit Bn} (h1 : WCl voc X ⟨a, Term.iri voc.sc, b⟩)
    (h2 : WCl voc X ⟨x, Term.iri voc.ty, a⟩) : WCl voc X ⟨x, Term.iri voc.ty, b⟩ := by
  refine WCl.step RuleId.r3b (fun v => match v with | RV.A => a | RV.B => b | _ => x)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2]

theorem w4a {p : Iri} {b x y : Term Iri Lit Bn}
    (h1 : WCl voc X ⟨Term.iri p, Term.iri voc.dom, b⟩)
    (h2 : WCl voc X ⟨x, Term.iri p, y⟩) : WCl voc X ⟨x, Term.iri voc.ty, b⟩ := by
  refine WCl.step RuleId.r4a
    (fun v => match v with | RV.A => Term.iri p | RV.B => b | RV.X => x | _ => y)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2]

theorem w4b {p : Iri} {b x y : Term Iri Lit Bn}
    (h1 : WCl voc X ⟨Term.iri p, Term.iri voc.range, b⟩)
    (h2 : WCl voc X ⟨x, Term.iri p, y⟩) : WCl voc X ⟨y, Term.iri voc.ty, b⟩ := by
  refine WCl.step RuleId.r4b
    (fun v => match v with | RV.A => Term.iri p | RV.B => b | RV.X => x | _ => y)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl
    exacts [h1, h2]

theorem w5a {p : Iri} {a b x y : Term Iri Lit Bn}
    (h1 : WCl voc X ⟨a, Term.iri voc.dom, b⟩)
    (h2 : WCl voc X ⟨Term.iri p, Term.iri voc.sp, a⟩)
    (h3 : WCl voc X ⟨x, Term.iri p, y⟩) : WCl voc X ⟨x, Term.iri voc.ty, b⟩ := by
  refine WCl.step RuleId.r5a
    (fun v => match v with
      | RV.A => a | RV.B => b | RV.C => Term.iri p | RV.X => x | RV.Y => y)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl | rfl
    exacts [h1, h2, h3]

theorem w5b {p : Iri} {a b x y : Term Iri Lit Bn}
    (h1 : WCl voc X ⟨a, Term.iri voc.range, b⟩)
    (h2 : WCl voc X ⟨Term.iri p, Term.iri voc.sp, a⟩)
    (h3 : WCl voc X ⟨x, Term.iri p, y⟩) : WCl voc X ⟨y, Term.iri voc.ty, b⟩ := by
  refine WCl.step RuleId.r5b
    (fun v => match v with
      | RV.A => a | RV.B => b | RV.C => Term.iri p | RV.X => x | RV.Y => y)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    rcases ht with rfl | rfl | rfl
    exacts [h1, h2, h3]

theorem w6a {p : Iri} {x y : Term Iri Lit Bn} (h : WCl voc X ⟨x, Term.iri p, y⟩) :
    WCl voc X ⟨Term.iri p, Term.iri voc.sp, Term.iri p⟩ := by
  refine WCl.step RuleId.r6a (fun v => match v with | RV.A => Term.iri p | RV.X => x | _ => y)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w6b1 {a b : Term Iri Lit Bn} (h : WCl voc X ⟨a, Term.iri voc.sp, b⟩) :
    WCl voc X ⟨a, Term.iri voc.sp, a⟩ := by
  refine WCl.step RuleId.r6b1 (fun v => match v with | RV.A => a | _ => b) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w6b2 {a b : Term Iri Lit Bn} (h : WCl voc X ⟨a, Term.iri voc.sp, b⟩) :
    WCl voc X ⟨b, Term.iri voc.sp, b⟩ := by
  refine WCl.step RuleId.r6b2 (fun v => match v with | RV.A => a | _ => b) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w6c (p : Kw) :
    WCl voc X ⟨Term.iri (voc.kw p), Term.iri voc.sp, Term.iri (voc.kw p)⟩ := by
  refine WCl.step (RuleId.r6c p) (fun _ => Term.iri voc.sp) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
  · intro t ht
    rho_simp at ht

theorem w6dDom {a x : Term Iri Lit Bn} (h : WCl voc X ⟨a, Term.iri voc.dom, x⟩) :
    WCl voc X ⟨a, Term.iri voc.sp, a⟩ := by
  refine WCl.step RuleId.r6dDom (fun v => match v with | RV.A => a | _ => x) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w6dRange {a x : Term Iri Lit Bn} (h : WCl voc X ⟨a, Term.iri voc.range, x⟩) :
    WCl voc X ⟨a, Term.iri voc.sp, a⟩ := by
  refine WCl.step RuleId.r6dRange (fun v => match v with | RV.A => a | _ => x)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w7a1 {a b : Term Iri Lit Bn} (h : WCl voc X ⟨a, Term.iri voc.sc, b⟩) :
    WCl voc X ⟨a, Term.iri voc.sc, a⟩ := by
  refine WCl.step RuleId.r7a1 (fun v => match v with | RV.A => a | _ => b) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w7a2 {a b : Term Iri Lit Bn} (h : WCl voc X ⟨a, Term.iri voc.sc, b⟩) :
    WCl voc X ⟨b, Term.iri voc.sc, b⟩ := by
  refine WCl.step RuleId.r7a2 (fun v => match v with | RV.A => a | _ => b) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w7bDom {a x : Term Iri Lit Bn} (h : WCl voc X ⟨x, Term.iri voc.dom, a⟩) :
    WCl voc X ⟨a, Term.iri voc.sc, a⟩ := by
  refine WCl.step RuleId.r7bDom (fun v => match v with | RV.A => a | _ => x) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w7bRange {a x : Term Iri Lit Bn} (h : WCl voc X ⟨x, Term.iri voc.range, a⟩) :
    WCl voc X ⟨a, Term.iri voc.sc, a⟩ := by
  refine WCl.step RuleId.r7bRange (fun v => match v with | RV.A => a | _ => x)
    ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

theorem w7bTy {a x : Term Iri Lit Bn} (h : WCl voc X ⟨x, Term.iri voc.ty, a⟩) :
    WCl voc X ⟨a, Term.iri voc.sc, a⟩ := by
  refine WCl.step RuleId.r7bTy (fun v => match v with | RV.A => a | _ => x) ?_ ⟨_, rfl⟩ rfl ?_
  · intro t ht
    rho_simp at ht
    subst ht
    exact ⟨_, rfl⟩
  · intro t ht
    rho_simp at ht
    subst ht
    exact h

end WellFormedRules

section Conservative

/-- What the induction keeps for each triple `t` of the generalized closure.  If the
predicate of `t` is an IRI, `t` is in the well-formed closure.  If it is not, there is an
IRI `a` such that the triple with `a` in place of the predicate is in the well-formed
closure, and so is `a sp p`, where `p` is the predicate of `t`. -/
def Inv (voc : Vocab Iri) (X : Graph Iri Lit Bn) (t : Triple (Term Iri Lit Bn)) : Prop :=
  (IriPred t → WCl voc X t) ∧
  (¬ IriPred t → ∃ a : Iri, WCl voc X ⟨t.s, Term.iri a, t.o⟩ ∧
    WCl voc X ⟨Term.iri a, Term.iri voc.sp, t.p⟩)

variable {voc : Vocab Iri} {X : Graph Iri Lit Bn}

theorem inv_kw {s o : Term Iri Lit Bn} {k : Iri} (h : WCl voc X ⟨s, Term.iri k, o⟩) :
    Inv voc X ⟨s, Term.iri k, o⟩ :=
  ⟨fun _ => h, fun hn => (hn ⟨k, rfl⟩).elim⟩

theorem wcl_of_inv_kw {s o : Term Iri Lit Bn} {k : Iri} (h : Inv voc X ⟨s, Term.iri k, o⟩) :
    WCl voc X ⟨s, Term.iri k, o⟩ :=
  h.1 ⟨k, rfl⟩

/-- From the invariant at `x a y`: an IRI `p` with `x p y` in the well-formed closure, where
`a` is `p` or `p sp a` is in that closure. -/
theorem inv_pred {x a y : Term Iri Lit Bn} (h : Inv voc X ⟨x, a, y⟩) :
    ∃ p : Iri, WCl voc X ⟨x, Term.iri p, y⟩ ∧
      (a = Term.iri p ∨ WCl voc X ⟨Term.iri p, Term.iri voc.sp, a⟩) := by
  by_cases hA : IriPred (⟨x, a, y⟩ : Triple (Term Iri Lit Bn))
  · obtain ⟨p, hp⟩ := hA
    have hp' : a = Term.iri p := hp
    subst hp'
    exact ⟨p, h.1 ⟨p, rfl⟩, Or.inl rfl⟩
  · obtain ⟨p, h1, h2⟩ := h.2 hA
    exact ⟨p, h1, Or.inr h2⟩

theorem sp_lift {p : Iri} {a b : Term Iri Lit Bn}
    (h : a = Term.iri p ∨ WCl voc X ⟨Term.iri p, Term.iri voc.sp, a⟩)
    (hab : WCl voc X ⟨a, Term.iri voc.sp, b⟩) :
    WCl voc X ⟨Term.iri p, Term.iri voc.sp, b⟩ := by
  rcases h with rfl | h
  · exact hab
  · exact w2a h hab

local macro "rho_simp" "at" h:ident : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw] at $h:ident)

local macro "rho_mem" : tactic =>
  `(tactic| simp [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw])

/-- The invariant holds of every triple of the generalized closure of a graph whose
predicates are IRIs. -/
theorem inv_of_cl (hV : voc.In V) (hX : ∀ t ∈ X, IriPred t) :
    ∀ c, Cl (rhoRegime voc hV) X c → ∀ t, c = some t → Inv voc X t := by
  intro c hc
  induction hc with
  | @base t ht =>
    intro t' h
    obtain rfl : t = t' := Option.some.inj h
    exact ⟨fun _ => WCl.base ht, fun hn => (hn (hX t ht)).elim⟩
  | @step r hr _ ih =>
    intro t hc
    obtain ⟨_, ⟨i, rfl⟩, θ, rfl⟩ := hr
    have ih' : ∀ a ∈ ((rule voc i).inst θ).prem, Inv voc X a := fun a ha => ih a ha a rfl
    cases i with
    | r2a =>
      have h1 := ih' ⟨θ RV.A, Term.iri voc.sp, θ RV.B⟩ (by rho_mem)
      have h2 := ih' ⟨θ RV.B, Term.iri voc.sp, θ RV.C⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      exact inv_kw (w2a (wcl_of_inv_kw h1) (wcl_of_inv_kw h2))
    | r2b =>
      have h1 := ih' ⟨θ RV.A, Term.iri voc.sp, θ RV.B⟩ (by rho_mem)
      have h2 := ih' ⟨θ RV.X, θ RV.A, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      obtain ⟨p, hxy, hpa⟩ := inv_pred h2
      have hpb := sp_lift hpa (wcl_of_inv_kw h1)
      refine ⟨fun hB => ?_, fun _ => ⟨p, hxy, hpb⟩⟩
      obtain ⟨q, hq⟩ := hB
      have hq' : θ RV.B = Term.iri q := hq
      rw [hq'] at hpb ⊢
      exact w2b hpb hxy
    | r3a =>
      have h1 := ih' ⟨θ RV.A, Term.iri voc.sc, θ RV.B⟩ (by rho_mem)
      have h2 := ih' ⟨θ RV.B, Term.iri voc.sc, θ RV.C⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      exact inv_kw (w3a (wcl_of_inv_kw h1) (wcl_of_inv_kw h2))
    | r3b =>
      have h1 := ih' ⟨θ RV.A, Term.iri voc.sc, θ RV.B⟩ (by rho_mem)
      have h2 := ih' ⟨θ RV.X, Term.iri voc.ty, θ RV.A⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      exact inv_kw (w3b (wcl_of_inv_kw h1) (wcl_of_inv_kw h2))
    | r4a =>
      have h1 := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.dom, θ RV.B⟩ (by rho_mem))
      have h2 := ih' ⟨θ RV.X, θ RV.A, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      obtain ⟨p, hxy, hpa | hpa⟩ := inv_pred h2
      · rw [hpa] at h1
        exact inv_kw (w4a h1 hxy)
      · exact inv_kw (w5a h1 hpa hxy)
    | r4b =>
      have h1 := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.range, θ RV.B⟩ (by rho_mem))
      have h2 := ih' ⟨θ RV.X, θ RV.A, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      obtain ⟨p, hxy, hpa | hpa⟩ := inv_pred h2
      · rw [hpa] at h1
        exact inv_kw (w4b h1 hxy)
      · exact inv_kw (w5b h1 hpa hxy)
    | r5a =>
      have h1 := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.dom, θ RV.B⟩ (by rho_mem))
      have h2 := wcl_of_inv_kw (ih' ⟨θ RV.C, Term.iri voc.sp, θ RV.A⟩ (by rho_mem))
      have h3 := ih' ⟨θ RV.X, θ RV.C, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      obtain ⟨p, hxy, hpc⟩ := inv_pred h3
      exact inv_kw (w5a h1 (sp_lift hpc h2) hxy)
    | r5b =>
      have h1 := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.range, θ RV.B⟩ (by rho_mem))
      have h2 := wcl_of_inv_kw (ih' ⟨θ RV.C, Term.iri voc.sp, θ RV.A⟩ (by rho_mem))
      have h3 := ih' ⟨θ RV.X, θ RV.C, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      obtain ⟨p, hxy, hpc⟩ := inv_pred h3
      exact inv_kw (w5b h1 (sp_lift hpc h2) hxy)
    | r6a =>
      have h := ih' ⟨θ RV.X, θ RV.A, θ RV.Y⟩ (by rho_mem)
      rho_simp at hc
      subst hc
      obtain ⟨p, hxy, hpa | hpa⟩ := inv_pred h
      · rw [hpa]
        exact inv_kw (w6a hxy)
      · exact inv_kw (w6b2 hpa)
    | r6b1 =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.sp, θ RV.B⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w6b1 h)
    | r6b2 =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.sp, θ RV.B⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w6b2 h)
    | r6c p =>
      rho_simp at hc
      subst hc
      exact inv_kw (w6c p)
    | r6dDom =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.dom, θ RV.X⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w6dDom h)
    | r6dRange =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.range, θ RV.X⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w6dRange h)
    | r7a1 =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.sc, θ RV.B⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w7a1 h)
    | r7a2 =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.A, Term.iri voc.sc, θ RV.B⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w7a2 h)
    | r7bDom =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.X, Term.iri voc.dom, θ RV.A⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w7bDom h)
    | r7bRange =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.X, Term.iri voc.range, θ RV.A⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w7bRange h)
    | r7bTy =>
      have h := wcl_of_inv_kw (ih' ⟨θ RV.X, Term.iri voc.ty, θ RV.A⟩ (by rho_mem))
      rho_simp at hc
      subst hc
      exact inv_kw (w7bTy h)

/-- **The generalized closure adds no triple with an IRI as predicate.**  On a graph whose
predicates are IRIs, a triple of the closure under all instances of rules (2) to (7) that
has an IRI as predicate is in the closure under the well-formed instances. -/
theorem wcl_of_mem_clPos (hV : voc.In V) (hX : ∀ t ∈ X, IriPred t)
    {t : Triple (Term Iri Lit Bn)} (ht : t ∈ (rhoRegime voc hV).clPos X) (hp : IriPred t) :
    WCl voc X t :=
  (inv_of_cl hV hX (some t) ht t rfl).1 hp

/-- The well-formed closure is inside the generalized closure, for every graph. -/
theorem mem_clPos_of_wcl (hV : voc.In V) {t : Triple (Term Iri Lit Bn)}
    (h : WCl voc X t) : t ∈ (rhoRegime (Bn := Bn) voc hV).clPos X := by
  induction h with
  | base ht => exact Cl.base ht
  | step i θ _ _ hc _ ih =>
    have hr : (rule voc i).inst θ ∈ (rhoRegime (Bn := Bn) voc hV).rules :=
      ⟨rule voc i, ⟨i, rfl⟩, θ, rfl⟩
    have h := Cl.step (X := X) hr ih
    rw [hc] at h
    exact h

/-- An instance of a graph whose predicates are IRIs has IRIs as predicates. -/
theorem iriPred_inst {H : Graph Iri Lit Bn} (hH : ∀ t ∈ H, IriPred t)
    (μ : Bn → Term Iri Lit Bn) : ∀ t ∈ H.inst μ, IriPred t := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨i, hi⟩ := hH h hh
  refine ⟨i, ?_⟩
  show Term.subst μ h.p = Term.iri i
  rw [hi]
  rfl

/-- **The two closures simply entail the same graphs whose predicates are IRIs.** -/
theorem simpleEntails_clPos_iff_wcl (hV : voc.In V) (hX : ∀ t ∈ X, IriPred t)
    {H : Graph Iri Lit Bn} (hH : ∀ t ∈ H, IriPred t) :
    SimpleEntails ((rhoRegime voc hV).clPos X) H ↔ SimpleEntails {t | WCl voc X t} H := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨μ, fun t ht => wcl_of_mem_clPos hV hX (hμ ht) (iriPred_inst hH μ t ht)⟩
  · rintro ⟨μ, hμ⟩
    exact ⟨μ, fun t ht => mem_clPos_of_wcl hV (hμ ht)⟩

/-- **Theorem 2 for the ρdf rules, with the paper's closure.**  For graphs `G` and `H` whose
predicates are IRIs, implication in the models fit for the base of rules (2) to (7) holds
from `G` to `H` iff the closure of `G` under the well-formed instances of those rules simply
entails `H`. -/
theorem rho_recovery_wellFormed (hV : voc.In V) {N : Set (Term Iri Lit Bn)}
    {G H : Graph Iri Lit Bn} (hG : ∀ t ∈ G, IriPred t) (hH : ∀ t ∈ H, IriPred t)
    (hA : Admissible N G H V) :
    FitEnt ((rhoRegime voc hV).base N) G H ↔ SimpleEntails {t | WCl voc G t} H :=
  (rho_recovery voc hV hA).trans (simpleEntails_clPos_iff_wcl hV hG hH)

end Conservative

end RhoDf
end ISRDF
