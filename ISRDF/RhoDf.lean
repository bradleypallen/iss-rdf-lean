import ISRDF.Patterns
import ISRDF.OntologyRelative

/-!
# The ρdf rules as a regime

New declarations only; nothing earlier in the library is changed.

Muñoz, Pérez and Gutierrez, "Simple and efficient minimal RDFS" (Journal of Web Semantics
7(3), 2009), define the fragment ρdf of RDFS, whose vocabulary is `sp`, `sc`, `type`, `dom`
and `range` (subPropertyOf, subClassOf, type, domain, range), and give deductive rules for
it in their Table 1.  Rule (1) is simple entailment.  Rules (2) to (7) are Horn rules over
triples.  This file writes rules (2) to (7) as pattern rules and shows that their ground
instances form a `Regime`, so that Theorem 2 applies.

What is checked here: that the rule set, as transcribed below, is a regime, and what
follows from Theorem 2 and from the ontology-relative corollary for it.  What is not
checked here: that the transcription agrees with the paper's table, and the paper's own
theorems that relate these rules to RDFS entailment (its Theorem 8, Corollary 9,
Theorem 10 and Corollary 18).  Those are cited, not formalized.

Three differences from the paper's table.

* A rule with two conclusions, (6b) and (7a), is two rules here.
* The schemas (6c), (6d) and (7b), which range over keywords, are one rule for each keyword.
* The paper instantiates a rule only where every resulting triple is a well-formed RDF
  triple.  The library works with generalized triples, so every instance is a rule here.

Contents.

* `Vocab` is the five keywords as IRIs; `Vocab.In` says they lie in `V`.
* `RuleId` names the 23 rules; `rule` gives each as a pattern rule; `rule_wf` is
  well-formedness.
* `rhoRegime` is rules (2) to (7).  `mrdfRegime` is rules (2), (3) and (4) only, the
  rules of the paper's minimal system for graphs that are ground and have no keyword as
  subject or object.
* `rho_recovery` and `mrdf_recovery` are Theorem 2 for them.  `rho_ontology_recovery` and
  `mrdf_ontology_recovery` add an ontology, by the ontology-relative corollary.
* `mrdf_sc_type` and `mrdf_sp_inherit` are two checks that the transcribed rules fire as
  rules (3b) and (2b) should.
-/

set_option autoImplicit false

namespace ISRDF
namespace RhoDf

variable {Iri Lit Bn : Type} {V : Set Iri}

/-- The five keywords of ρdf. -/
inductive Kw
  | sp | sc | ty | dom | range

/-- The ρdf vocabulary as IRIs. -/
structure Vocab (Iri : Type) where
  sp : Iri
  sc : Iri
  ty : Iri
  dom : Iri
  range : Iri

/-- The IRI of a keyword. -/
def Vocab.kw (voc : Vocab Iri) : Kw → Iri
  | Kw.sp => voc.sp
  | Kw.sc => voc.sc
  | Kw.ty => voc.ty
  | Kw.dom => voc.dom
  | Kw.range => voc.range

/-- The five keywords lie in `V`. -/
def Vocab.In (voc : Vocab Iri) (V : Set Iri) : Prop := ∀ k, voc.kw k ∈ V

/-- The variables of the rules, with the paper's letters. -/
inductive RV
  | A | B | C | X | Y

/-- The rules (2) to (7) of the paper's Table 1, one name for each Horn rule. -/
inductive RuleId
  | r2a | r2b | r3a | r3b | r4a | r4b | r5a | r5b
  | r6a | r6b1 | r6b2 | r6c (p : Kw) | r6dDom | r6dRange
  | r7a1 | r7a2 | r7bDom | r7bRange | r7bTy

/-- Rules (2), (3) and (4): the rules of the paper's minimal system. -/
def RuleId.Core : RuleId → Prop
  | r2a | r2b | r3a | r3b | r4a | r4b => True
  | _ => False

section Rules
variable (voc : Vocab Iri)

local notation "𝐴" => (PTerm.var RV.A : PTerm RV Iri Lit)
local notation "𝐵" => (PTerm.var RV.B : PTerm RV Iri Lit)
local notation "𝐶" => (PTerm.var RV.C : PTerm RV Iri Lit)
local notation "𝑋" => (PTerm.var RV.X : PTerm RV Iri Lit)
local notation "𝑌" => (PTerm.var RV.Y : PTerm RV Iri Lit)

/-- A keyword as a pattern term. -/
abbrev kwt (k : Kw) : PTerm RV Iri Lit := PTerm.iri (voc.kw k)

/-- A triple pattern. -/
abbrev tp (s p o : PTerm RV Iri Lit) : PTriple RV Iri Lit := ⟨s, p, o⟩

/-- The pattern rule of each name, transcribed from the paper's Table 1. -/
def rule : RuleId → PRule RV Iri Lit
  -- (2) Subproperty
  | .r2a => ⟨{tp 𝐴 (kwt voc .sp) 𝐵, tp 𝐵 (kwt voc .sp) 𝐶}, some (tp 𝐴 (kwt voc .sp) 𝐶)⟩
  | .r2b => ⟨{tp 𝐴 (kwt voc .sp) 𝐵, tp 𝑋 𝐴 𝑌}, some (tp 𝑋 𝐵 𝑌)⟩
  -- (3) Subclass
  | .r3a => ⟨{tp 𝐴 (kwt voc .sc) 𝐵, tp 𝐵 (kwt voc .sc) 𝐶}, some (tp 𝐴 (kwt voc .sc) 𝐶)⟩
  | .r3b => ⟨{tp 𝐴 (kwt voc .sc) 𝐵, tp 𝑋 (kwt voc .ty) 𝐴}, some (tp 𝑋 (kwt voc .ty) 𝐵)⟩
  -- (4) Typing
  | .r4a => ⟨{tp 𝐴 (kwt voc .dom) 𝐵, tp 𝑋 𝐴 𝑌}, some (tp 𝑋 (kwt voc .ty) 𝐵)⟩
  | .r4b => ⟨{tp 𝐴 (kwt voc .range) 𝐵, tp 𝑋 𝐴 𝑌}, some (tp 𝑌 (kwt voc .ty) 𝐵)⟩
  -- (5) Implicit typing
  | .r5a => ⟨{tp 𝐴 (kwt voc .dom) 𝐵, tp 𝐶 (kwt voc .sp) 𝐴, tp 𝑋 𝐶 𝑌},
      some (tp 𝑋 (kwt voc .ty) 𝐵)⟩
  | .r5b => ⟨{tp 𝐴 (kwt voc .range) 𝐵, tp 𝐶 (kwt voc .sp) 𝐴, tp 𝑋 𝐶 𝑌},
      some (tp 𝑌 (kwt voc .ty) 𝐵)⟩
  -- (6) Subproperty reflexivity
  | .r6a => ⟨{tp 𝑋 𝐴 𝑌}, some (tp 𝐴 (kwt voc .sp) 𝐴)⟩
  | .r6b1 => ⟨{tp 𝐴 (kwt voc .sp) 𝐵}, some (tp 𝐴 (kwt voc .sp) 𝐴)⟩
  | .r6b2 => ⟨{tp 𝐴 (kwt voc .sp) 𝐵}, some (tp 𝐵 (kwt voc .sp) 𝐵)⟩
  | .r6c p => ⟨∅, some (tp (kwt voc p) (kwt voc .sp) (kwt voc p))⟩
  | .r6dDom => ⟨{tp 𝐴 (kwt voc .dom) 𝑋}, some (tp 𝐴 (kwt voc .sp) 𝐴)⟩
  | .r6dRange => ⟨{tp 𝐴 (kwt voc .range) 𝑋}, some (tp 𝐴 (kwt voc .sp) 𝐴)⟩
  -- (7) Subclass reflexivity
  | .r7a1 => ⟨{tp 𝐴 (kwt voc .sc) 𝐵}, some (tp 𝐴 (kwt voc .sc) 𝐴)⟩
  | .r7a2 => ⟨{tp 𝐴 (kwt voc .sc) 𝐵}, some (tp 𝐵 (kwt voc .sc) 𝐵)⟩
  | .r7bDom => ⟨{tp 𝑋 (kwt voc .dom) 𝐴}, some (tp 𝐴 (kwt voc .sc) 𝐴)⟩
  | .r7bRange => ⟨{tp 𝑋 (kwt voc .range) 𝐴}, some (tp 𝐴 (kwt voc .sc) 𝐴)⟩
  | .r7bTy => ⟨{tp 𝑋 (kwt voc .ty) 𝐴}, some (tp 𝐴 (kwt voc .sc) 𝐴)⟩

end Rules

/-- Every rule is well-formed over a `V` that contains the five keywords. -/
theorem rule_wf {voc : Vocab Iri} (hV : voc.In V) (i : RuleId) :
    (rule (Lit := Lit) voc i).WF V := by
  have h1 := hV Kw.sp
  have h2 := hV Kw.sc
  have h3 := hV Kw.ty
  have h4 := hV Kw.dom
  have h5 := hV Kw.range
  constructor
  · cases i <;>
      simp [rule, PGraph.Over, PTerm.Const, Triple.terms, h1, h2, h3, h4, h5]
  · cases i <;>
      simp [rule, ConclOK, Triple.terms, h1, h2, h3]
    exact hV _

/-- No rule concludes `⊥`. -/
theorem rule_concl_ne_none (voc : Vocab Iri) (i : RuleId) :
    (rule (Lit := Lit) voc i).concl ≠ none := by
  cases i <;> simp [rule]

/-- A regime of pattern rules none of which concludes `⊥` has no inconsistent graph. -/
theorem patternRegime_not_inconsistent {Var : Type} {S : Set (PRule Var Iri Lit)}
    {hS : ∀ r ∈ S, r.WF V} (h : ∀ r ∈ S, r.concl ≠ none) (X : Graph Iri Lit Bn) :
    ¬ (patternRegime (Bn := Bn) S hS).Inconsistent X := by
  have key : ∀ c, Cl (patternRegime (Bn := Bn) S hS) X c → c ≠ none := by
    intro c hc
    induction hc with
    | base _ => simp
    | step hr _ _ =>
      obtain ⟨r, hrS, θ, rfl⟩ := hr
      intro hn
      have hn' : Option.map (Triple.map (PTerm.eval θ)) r.concl = none := hn
      exact h r hrS (Option.map_eq_none_iff.1 hn')
  exact fun hX => key none hX rfl

/-- The regime of rules (2) to (7). -/
def rhoRegime (voc : Vocab Iri) (hV : voc.In V) : Regime Iri Lit Bn V :=
  patternRegime (Set.range (rule voc)) (by
    rintro _ ⟨i, rfl⟩
    exact rule_wf hV i)

/-- The regime of rules (2), (3) and (4). -/
def mrdfRegime (voc : Vocab Iri) (hV : voc.In V) : Regime Iri Lit Bn V :=
  patternRegime (rule voc '' {i | i.Core}) (by
    rintro _ ⟨i, -, rfl⟩
    exact rule_wf hV i)

section Results
variable (voc : Vocab Iri) (hV : voc.In V)

theorem rho_not_inconsistent (X : Graph Iri Lit Bn) :
    ¬ (rhoRegime (Lit := Lit) (Bn := Bn) voc hV).Inconsistent X :=
  patternRegime_not_inconsistent (by
    rintro _ ⟨i, rfl⟩
    exact rule_concl_ne_none voc i) X

theorem mrdf_not_inconsistent (X : Graph Iri Lit Bn) :
    ¬ (mrdfRegime (Lit := Lit) (Bn := Bn) voc hV).Inconsistent X :=
  patternRegime_not_inconsistent (by
    rintro _ ⟨i, -, rfl⟩
    exact rule_concl_ne_none voc i) X

variable {N : Set (Term Iri Lit Bn)}

/-- **Theorem 2 for the ρdf rules.**  Implication in the models fit for the base of rules
(2) to (7) holds from `G` to `H` iff the closure of `G` under those rules simply entails
`H`. -/
theorem rho_recovery {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) :
    FitEnt ((rhoRegime voc hV).base N) G H ↔
      SimpleEntails ((rhoRegime voc hV).clPos G) H :=
  (closure_regimes (rhoRegime voc hV) hA).trans
    ⟨fun h => h.resolve_left (rho_not_inconsistent voc hV G), Or.inr⟩

/-- **Theorem 2 for rules (2), (3) and (4).** -/
theorem mrdf_recovery {G H : Graph Iri Lit Bn} (hA : Admissible N G H V) :
    FitEnt ((mrdfRegime voc hV).base N) G H ↔
      SimpleEntails ((mrdfRegime voc hV).clPos G) H :=
  (closure_regimes (mrdfRegime voc hV) hA).trans
    ⟨fun h => h.resolve_left (mrdf_not_inconsistent voc hV G), Or.inr⟩

/-- **The ρdf rules with an ontology.**  With a schema `O` held fixed, implication from `G`
to `H` holds iff the closure of `G ∪ O` under rules (2) to (7) simply entails `H`. -/
theorem rho_ontology_recovery (O : Graph Iri Lit Bn) (hO : O.IriOnly) {G H : Graph Iri Lit Bn}
    (hA : Admissible N G H (V ∪ O.iris)) :
    FitEnt (((rhoRegime voc hV).withOntology O hO).base N) G H ↔
      SimpleEntails ((rhoRegime voc hV).clPos (G ∪ O)) H :=
  ((rhoRegime voc hV).ontology_relative O hO hA).trans
    ⟨fun h => h.resolve_left (rho_not_inconsistent voc hV (G ∪ O)), Or.inr⟩

/-- **Rules (2), (3) and (4) with an ontology.** -/
theorem mrdf_ontology_recovery (O : Graph Iri Lit Bn) (hO : O.IriOnly)
    {G H : Graph Iri Lit Bn} (hA : Admissible N G H (V ∪ O.iris)) :
    FitEnt (((mrdfRegime voc hV).withOntology O hO).base N) G H ↔
      SimpleEntails ((mrdfRegime voc hV).clPos (G ∪ O)) H :=
  ((mrdfRegime voc hV).ontology_relative O hO hA).trans
    ⟨fun h => h.resolve_left (mrdf_not_inconsistent voc hV (G ∪ O)), Or.inr⟩

/-- A check on the transcription: rule (3b) fires.  From `a sc b` and `x type a`, the
closure has `x type b`. -/
theorem mrdf_sc_type {X : Graph Iri Lit Bn} {a b x : Term Iri Lit Bn}
    (h1 : (⟨a, Term.iri voc.sc, b⟩ : Triple (Term Iri Lit Bn)) ∈ X)
    (h2 : (⟨x, Term.iri voc.ty, a⟩ : Triple (Term Iri Lit Bn)) ∈ X) :
    (⟨x, Term.iri voc.ty, b⟩ : Triple (Term Iri Lit Bn)) ∈ (mrdfRegime voc hV).clPos X := by
  let θ : RV → Term Iri Lit Bn := fun v =>
    match v with
    | RV.A => a
    | RV.B => b
    | _ => x
  have hr : (rule voc RuleId.r3b).inst θ ∈ (mrdfRegime (Bn := Bn) voc hV).rules :=
    ⟨rule voc RuleId.r3b, ⟨RuleId.r3b, trivial, rfl⟩, θ, rfl⟩
  have hc := Cl.step (X := X) hr (by
    intro t ht
    have ht' : t = ⟨a, Term.iri voc.sc, b⟩ ∨ t = ⟨x, Term.iri voc.ty, a⟩ := by
      simpa [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw, θ, eq_comm]
        using ht
    rcases ht' with rfl | rfl
    · exact Cl.base h1
    · exact Cl.base h2)
  exact hc

/-- A check on the transcription: rule (2b) fires, with a variable in predicate position.
From `p sp q` and `x p y`, the closure has `x q y`. -/
theorem mrdf_sp_inherit {X : Graph Iri Lit Bn} {p q x y : Term Iri Lit Bn}
    (h1 : (⟨p, Term.iri voc.sp, q⟩ : Triple (Term Iri Lit Bn)) ∈ X)
    (h2 : (⟨x, p, y⟩ : Triple (Term Iri Lit Bn)) ∈ X) :
    (⟨x, q, y⟩ : Triple (Term Iri Lit Bn)) ∈ (mrdfRegime voc hV).clPos X := by
  let θ : RV → Term Iri Lit Bn := fun v =>
    match v with
    | RV.A => p
    | RV.B => q
    | RV.X => x
    | _ => y
  have hr : (rule voc RuleId.r2b).inst θ ∈ (mrdfRegime (Bn := Bn) voc hV).rules :=
    ⟨rule voc RuleId.r2b, ⟨RuleId.r2b, trivial, rfl⟩, θ, rfl⟩
  have hc := Cl.step (X := X) hr (by
    intro t ht
    have ht' : t = ⟨p, Term.iri voc.sp, q⟩ ∨ t = ⟨x, p, y⟩ := by
      simpa [PRule.inst, PGraph.inst, rule, Triple.map, PTerm.eval, Vocab.kw, θ, eq_comm]
        using ht
    rcases ht' with rfl | rfl
    · exact Cl.base h1
    · exact Cl.base h2)
  exact hc

end Results

end RhoDf
end ISRDF
