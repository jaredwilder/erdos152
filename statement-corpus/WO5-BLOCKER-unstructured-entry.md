# WO-5 blocker: an unstructured problem-database entry yields ZERO nodes

Measured 2026-08-28.

## What was run

Two closed Erdos problems were frozen as sources under `SOURCE-CONTRACT.json` and passed to
WO-1 (`oracle/frontier_formalizer/source_graph.py::build`).

    erdos-339.tex   523 bytes   sha256 2dea361e93e9b8e4...
    erdos-444.tex   314 bytes   sha256 d955fbb62686276e...

Result, both: **0 nodes, 0 edges.**

## Why

`extract_nodes` recognises statements by document structure and nothing else:

1. LaTeX theorem environments discovered from `\newtheorem` / `\declaretheorem`, or
2. markdown-style headers (`Theorem 1.`, `Lemma 2.`) over the regions no environment covers.

An erdosproblems.com entry has neither. It is one unlabelled paragraph that runs
question -> history -> resolution -> attribution with no markup between them. There is no
boundary to grab, so nothing is extracted.

This is a **correct refusal, not a crash**: the extractor invented no node. That matters,
because the failure mode this estate actually fears is a facade that produces a plausible
node from prose that does not contain one, which is exactly what the `_LATEX_DOC_RE` guard
was added to prevent on arXiv:2408.08514.

## The blocker, stated as WO-5 wants it

> Which observed failure prevented arbitrary mathematics from becoming Lean?

An entry in a problem database carries its claim as unstructured prose in which the
statement, its history and its resolution are not separated by any machine-readable marker.
Statement extraction is anchored on structure. No structure, no statement, no capsule, no
court, no Lean.

## Scope of the gap

From `erdos-problems-db-20260828.yaml` (teorth/erdosproblems `data/problems.yaml`,
sha256 c741a71d71ff1ae0a7d9fbeeba42caa80aa0fad1efb561c805726746cc314983):

| | count |
|---|---|
| problems in the database | 1217 |
| closed (proved / disproved / solved) | 556 |
| closed AND `formal_status: unformalized` AND absent from the local DeepMind formal-conjectures checkout | **247** |

The first 70 of those 247 were fetched and none carries the site's "formalised in Lean"
notice, which is an independent cross-check of the database field.

Two of the database's status fields do NOT agree with the page text (checked on #245, which
the yaml marks `unformalized` while the page states it is formalised as part of the DeepMind
project). The count above is therefore a **lower-confidence upper bound**, not a certified
figure, and any capability built against it must re-check per problem rather than trust the
column.

## What this does NOT justify building

It does not justify a general prose-understanding layer. The narrow capability the failure
argues for is an entry ingestor that splits a database entry into (question, resolution,
attribution) and emits typed nodes with byte-exact provenance, refusing when the split is
not determinable. Whether formalization ITSELF works on this input is a separate question
and is being measured independently by feeding the frozen text straight to WO-3.

---

# CORRECTION, same day: the diagnosis above was WRONG on its central claim

The section "Why" says an entry has no machine-readable boundary. That is false, and the
error was self-inflicted.

An erdosproblems.com page marks the original Erdos question inside its own `problem-text`
container and leaves the resolution as the tail. Measured across the 70 fetched entries, the
question boundary recovers **70/70**. The entry is structured. The `.tex` freeze was not:
the flattening step collapsed question, history and resolution into one paragraph and threw
the boundary away before WO-1 ever saw it.

So WO-1's zero-node result was a correct refusal on a source that had ALREADY been broken
upstream, not evidence that the source lacks structure. The extractor behaved correctly
throughout; the freezing step was the defect.

## What was built, and what measurement justified it

`oracle/frontier_formalizer/entry_ingest.py` (selftest 17/17). It ingests the RAW PAGE, so
provenance hashes cover what the site served rather than a lossy rewrite of it.

Run over all 70 fetched closed entries: **70/70 yield a question node and a resolution node,
with zero refusals.**

It refuses four ways rather than guessing: `NO_QUESTION_CONTAINER`, `EMPTY_QUESTION`,
`CONTAINER_BODY_DISAGREE`, `EMPTY_RESOLUTION`. The question node's byte range is an exact
slice and says so; the resolution spans sibling containers, so its range is declared
`"exactness": "region"` rather than passed off as exact.

It does NOT decide the direction of the resolution. Direction needs evidence and a court.
Entry #482's own text reads "The problem statement is open-ended", which is precisely the
case a direction classifier must be able to answer UNKNOWN on. A marker vocabulary over the
same 70 entries hit 60/70; the 10 misses all DO carry resolutions, phrased in ways the
vocabulary did not anticipate ("Yes, as shown by", "This is false", "A positive answer
follows from"). A 60/70 classifier that silently guesses on the other 10 would be worse than
no classifier.

## The lesson worth keeping

The freezing step is part of the machine and can destroy the very structure the extractor
needs. A source contract that pins a hash of a LOSSY rendering pins the wrong artifact. Freeze
what the source served.
