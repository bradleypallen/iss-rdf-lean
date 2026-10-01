# Pilot outline: a defeasible curation assistant for cultural heritage knowledge graphs

Working draft, 11 September 2026 — B. P. Allen (University of Amsterdam) for discussion with M. van Erp's team (KNAW Humanities Cluster / Meertens). Written as working notes, not as a letter; the framing sentences want re-voicing before this is sent.

---

## 1. The problem the pilot addresses

A curator working on a collection graph can find out that a record violates a constraint. Current tooling stops there. It does not say what would answer the challenge, does not let a proposed fix be tested before it is written, and has nowhere to put a curator's disagreement with an inference the system draws. Where the graph already contains contradictions — conflated records, merged sources — classical reasoning is unusable, so consistency checking is not run at all.

Underneath is a representational gap. RDF has no negation and no defeasibility, so the "unless" clauses that carry real curatorial judgement live in SHACL shapes and in `NOT EXISTS` guards inside SPARQL pipelines, where the semantics cannot see them.

## 2. What we would put in front of curators

A curation assistant built on pyNMMS, a reasoner for a nonmonotonic, bilateral consequence relation over an unchanged RDF store. Per flagged record it shows:

1. **The verdict** — identical to the SHACL verdict, since the shapes are the input.
2. **A rescue** — the defeater that would answer the challenge, named explicitly.
3. **A hypothetical** — the effect of a proposed fix, evaluated without writing a triple.
4. **A contest action** — the curator records that the inference does not hold for this case, as a denial in their own position rather than as an edit to the data.

Incoherence is attributed to a position, meaning a curator's own assertions against the store as background. Standing contradictions elsewhere in the store are inventory and do not block work.

### Evidence in hand (Amsterdam Museum collection data, 1,391 records, three constraints)

- Agreement with pySHACL and with the shapes' own SPARQL on every record.
- A rescue named for 1,052 of the 1,191 flagged records; every proposed fix restored coherence when run hypothetically.
- About seven times faster than validation, because the base reads the store's existing closure in place.
- Millisecond responses over a six-million-triple store.

(Figures from the September 2026 experiment record; absolute timings to be restated on fixed hardware before publication.)

## 3. Why this team

- **TRIFECTA** works on competing narratives across texts and time. "Consensus without merger" gives that a formal shape: intersect over models, license what both communities license, keep each base intact, and leave the disagreement visible as the pairs good in one model and not the other. Merging, forking and provenance annotations are the current options; none of them carries inferential weight.
- **Culturally Aware AI** is about polyvocality with curator oversight. Here the curator holds authority by construction: the system proposes, the curator disposes, and what the curator denies is recorded as content.
- **SABIO** looked at what collection metadata suppresses. There is a parallel finding in the life sciences: Gene Ontology curators publish 1,383 NOT annotations, and classical propagation commits 394 gene products to classes those curators explicitly denied. Published dissent, discarded by the infrastructure.

## 4. Design

**Collections.** Start with the Amsterdam Museum data already running, as a warm start and a demo. The pilot proper runs on one collection of their choosing, ideally one with existing SHACL shapes or SPARQL quality checks and access to its curators.

**Participants.** Four to six curators or collection data specialists. Three is a viable floor.

**Task.** Forty records per participant, split into two blocks of twenty, counterbalanced:

- **Block A (control):** current tooling — validation report plus the graph.
- **Block B:** the same records in the assistant, with rescue, hypothetical and contest.

Records are sampled from flagged cases, with a stratum of unflagged controls to catch over-acceptance.

**Gold standard.** Two senior curators, not participants, adjudicate the correct disposition of each record in advance, with disagreements recorded rather than resolved.

**Pre-registration.** Predictions and analysis plan committed to a dated repository before the first session. (We have done this once already, in the Gene Ontology run.)

## 5. Measures

**Primary**

- Accuracy against the gold standard, per block.
- Time per record, per block.
- Acceptance rate of proposed rescues, and the rate of accepting *wrong* rescues. This is the containment claim, and the number that decides whether the assistant helps. The comparison point is OE-Assist (Lippolis et al. 2025), where correct suggestions raised ontology engineers' accuracy by 13% and wrong ones lowered it by 28%.

**Secondary**

- System Usability Scale, plus a short exit interview.
- Use of *contest*: how often, on what, and what curators expect to happen to the record afterwards.
- Number of denials recorded — knowledge the current pipeline has no way to keep.

**Data-level, from the resulting base**

- Failures of Cut and Cautious Monotony. If a curated base from real practice is non-cumulative, that is a result for the logic side as well, and it decides whether the substructural machinery earns its keep on real data.

## 6. Effort and timeline (six months)

| Phase | Weeks | Work |
|---|---|---|
| 0. Scoping | 2 | Choose the collection; confirm curator access; ethics and data licensing |
| 1. Inputs | 4 | Translate existing shapes and query guards into base entries; agree the gold standard |
| 2. Tool | 6 | Curator-facing interface, decision logging, export of accepted fixes as SPARQL updates and of denials as records |
| 3. Sessions | 3 | Pilot sessions, think-aloud on a subset |
| 4. Analysis | 6 | Analysis, write-up, data release |

**Effort.** Allen: engineering, analysis, roughly 0.3 FTE across the period. Their side: one researcher at about 0.1 FTE for data access and recruitment; four hours per curator. An MSc student on the interface would suit the work if one is available.

## 7. Outputs

- A computational humanities or digital humanities paper on curator practice and contested records, led by their team.
- An ISWC in-use or resource paper on the assistant, joint.
- A released dataset of curator decisions, including denials, which does not exist for any collection today.
- Open-source tool and reproducible experiment record.
- On my side, the theoretical paper this instruments.

## 8. Scope limits, deliberately

- **No language model in the pilot.** The dialogue system (Elenchus) stays out. Shapes and existing guards supply the input; adding an LLM would confound the measurement.
- **No re-modelling.** Object language, store and shapes are unchanged.
- **No new ontology language.** Curators never see a proof rule.

## 9. Risks

| Risk | Mitigation |
|---|---|
| Curator time is scarce | Four hours each; sessions run where they work; forty records is a morning |
| The chosen collection has no shapes | Derive entries from existing SPARQL quality checks, which is the same translation |
| Rules with value guards (dates compared to dates) sit outside the current uniformity condition | Known limitation; handle those constraints as a documented special case |
| Small n | Report effect sizes and qualitative findings; treat this as a pilot that sizes a larger study |
| Logging curator decisions raises consent questions | Ethics review through their institution; participants review the released data |

## 10. Questions for their team

1. Which collection, and who owns the quality checks on it?
2. Are curators available as participants, or only as advisers?
3. Does TRIFECTA have a use case where two sources disagree and both must be kept? That is the sharpest test of the perspectives claim.
4. Would recording denials as publishable data be acceptable to the collection holder?
5. Who leads which paper?
