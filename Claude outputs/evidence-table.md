# Evidence table: pyNMMS against pySHACL and a classical reasoner

Assembled 11 September 2026 from *Implication-space semantics for knowledge engineers* (draft, 11 Sept, §9) and `PERFORMANCE.md` (measured 2026-09-06, pyNMMS 0.9.2). Every cell carries its source. Cells marked **[confirm]** were not in either document and need to come from `experiments/README.md` or a re-run before they go in a paper.

Column meanings:

- **pyNMMS** — NMMS over the base B_{R,S,D}, positions attributed to a holder.
- **SHACL / SPARQL** — what the community's existing validation and query tooling returns.
- **Classical reasoner** — RDFS or OWL 2 RL materialisation plus lookup (owlrl-class engine).

---

## 1. Gene Ontology: curators' negative knowledge

Setup: human GAF loaded, 6.4M asserted triples, 906,445 annotations, of which 1,383 are NOT. The annotation-propagation rule (a product annotated to a class is annotated to its superclasses) was placed once in the regime R and once in D as a licence defeated by a NOT annotation to the target class. Closure: ~8M triples. (Companion note §9.)

| Question a practitioner asks | pyNMMS | SHACL / SPARQL | Classical reasoner | Source |
|---|---|---|---|---|
| Does propagation commit products to classes curators denied? | With the rule in D: none by propagation | Not expressible as an entailment question | Yes: 394 products, materialised without comment | Note §9 |
| Of those, how many arise by propagation alone? | 0 | — | 59 | Note §9 |
| What remains after defeat is honoured? | 335 positions where the GAF asserts both a positive and a NOT annotation for the same product and class, each with its own evidence — incoherent positions for a curator to resolve | A hand-written query could find these pairs; nothing marks them as incoherent | Materialises both, no conflict reported | Note §9 |
| Do uncontradicted propagations still fire? | Yes, on a sample of 400 | — | Yes (all) | Note §9 |
| Were the counts predicted before the run? | Yes | — | — | Note §9; **[confirm]** with a dated commit |
| Cost per position | 1.5–47 ms over an 8M-triple closure | **[confirm]** | Lookup: microseconds after materialisation | Note §9 |
| Agreement with classical entailment where both are defined | 18/18 atomic, 5/5 pattern queries | — | baseline | Note §10 |
| Cost of the logical queries the classical stack cannot express | 8 queries at tens of µs; 1–2 ms when a new annotation is placed in the antecedent and propagated in process | Not expressible | Not expressible | Note §10 |
| Materialisation cost (one-time) | Same step as the classical reasoner | n/a | **[confirm]** measured time on this GAF | PERFORMANCE §2 gives 5,000–6,500 asserted triples/s in-process, so ~16–21 min at 6.4M — an extrapolation from synthetic data, not a measurement |

**The headline for practitioners:** 394 gene products are currently committed by classical propagation to classes their curators explicitly denied, 59 of them purely by propagation. Anyone running RDFS or OWL 2 RL propagation over GO annotations today silently contradicts the curation record, and no existing tool reports it.

**Open question to settle before publishing this section:** GO's documentation says NOT annotations propagate *down* the hierarchy and positive ones up, and that a positive plus a NOT on the same pair records unresolved conflicting findings. That fits reading NOT as a rejection inside a position rather than as a defeater in D. Check the 59 and the 335 against the GAF's `assigned_by` and reference columns: same assigner is one holder's incoherent position, different assigners is disagreement between sources.

---

## 2. Amsterdam Museum: constraints with defeaters

Setup: three constraints over 1,391 records — a record starting after it ends; a record with two production starts; an object made after its maker's death, unless the attribution is qualified, the maker's role is publisher or designer, or the impression is posthumous. Each stated twice: as SHACL-SPARQL shapes, and as incompatibilities in D whose defeaters are the shapes' `NOT EXISTS` clauses. (Companion note §9.)

| Question a practitioner asks | pyNMMS | SHACL / SPARQL | Classical reasoner | Source |
|---|---|---|---|---|
| Which records violate the constraints? | Same verdict on every record | Same verdict (pySHACL and the shapes' queries run natively) | Cannot express the constraints | Note §9 |
| Records covered | 1,391 | 1,391 | — | Note §9 |
| Flagged records | 1,191 **[confirm]** — 86% of the corpus is high; check whether this counts violations rather than records | same | — | Note §9 |
| What would answer this challenge? | Named a rescue for 1,052 of the 1,191 flagged records | Not offered: a report names a focus node and a constraint | — | Note §9 |
| Would this edit fix it? | Ran the proposed fix as a hypothetical, without writing a triple; coherence restored in every case | Only by editing the data and re-validating | — | Note §9 |
| What does this record commit its holder to by default? | Answered | Not expressible | Not expressible | Note §9 |
| Run time | About 7× faster than validation, since it reads the closure in place | baseline | — | Note §9; **[confirm]** absolute seconds for both |
| Behaviour on a store with standing contradictions | Incoherence attributed to a position: a conflated record makes that holder's position out of bounds, leaving the rest usable | Validation is per focus node, so the issue does not arise | Explosion: every query derivable | Note §9 |
| Interactive cost | Each question answered in milliseconds over 6M triples | **[confirm]** | — | Note §9 |

**The headline for practitioners:** the same verdicts as your validator, plus a proposed repair and a way to test it before writing anything, at a fraction of the time.

---

## 3. Cost and scale (synthetic data)

From `PERFORMANCE.md`. These answer "will it keep up?", not "does it find anything".

| Metric | pyNMMS | Classical reasoner |
|---|---|---|
| Atomic ASK, 3,010 → 300,010 asserted triples | 28–41 µs, flat | Lookup in the closure, also microseconds |
| Negation answered as incoherence | 52–84 µs in memory | Not expressible |
| Four-connective query | 117–187 µs | Not expressible |
| Incremental TELL (2 triples) | 0.45–0.73 ms | Comparable incremental maintenance |
| Largest store measured | 10⁷ asserted, 4×10⁷ closure (Oxigraph on disk); query cost flat from 250k closure triples upward | Same materialisation step |
| One-time materialisation | Under an hour at 10⁷ on disk | The same cost, measured the same way |
| RDFS materialisation rate, in-process | 5,000–6,500 asserted triples/s | Native engines (RDFox, GraphDB, Jena) are 2–3 orders faster; pyNMMS assumes the store materialises its own regime |
| Worst case | coNP-hard; ~2.17^k proof nodes in the number of connectives k; sub-second to about k = 13 | Polynomial in the closure |
| Hypothetical reasoning | 0.3–0.5 ms per added triple in memory; a round trip per rule firing over SPARQL | No counterpart |

---

## 4. What is missing before this table carries a paper

1. **Absolute timings for the museum comparison.** "7× faster" needs both numbers, on stated hardware, with the pySHACL version.
2. **The flagged-record count.** 1,191 of 1,391 needs to be confirmed as records rather than violations.
3. **GO materialisation time**, measured rather than extrapolated from the synthetic rate.
4. **A dated record of the pre-run predictions** (commit hash and timestamp).
5. **Cut and Cautious Monotony failures** counted in both bases. If real practice is non-cumulative, that is the strongest single result available to you, and it is a query pyNMMS can already answer.
6. **A curator in the loop.** The rescue and hypothetical columns are the product claim, and so far only the author has used them. Three curators on GO, measured OE-Assist style (accuracy with and without, time per accepted fix), would convert the claim into evidence.
7. **A run against a defeasible comparator**, not just against classical and SHACL: the same museum constraints under defeasible RDFS (rational closure) or an ASP encoding. Reviewers will ask what the substructural base buys over a cumulative one.
