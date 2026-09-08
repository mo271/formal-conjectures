---
name: review-pr
description: >-
  Review a pull request for the google-deepmind/formal-conjectures repository.
  Use when the user asks to review a PR (e.g., "review pr 4792", "review PR #4850",
  or "carefully review FormalConjectures/..."). Fetches the PR branch, inspects changed files,
  fetches existing PR discussion/review comments from GitHub, verifies mathematical faithfulness
  against source literature (arXiv, Erdős problems, papers, Wikipedia), checks repository guidelines
  (AGENTS.md, subfolder READMEs, imports, ForMathlib separation), tests Lean compilation,
  and produces a structured review artifact without modifying files or pushing upstream.
---

# Formal Conjectures PR Review Runbook

This skill automates the rigorous mathematical and stylistic review of Pull Requests submitted to the `google-deepmind/formal-conjectures` repository.

> [!IMPORTANT]
> **READ-ONLY / NO PUSH POLICY:**
> During the review process, **DO NOT alter workspace files** in the PR branch (unless explicitly instructed by the user to test a proof locally) and **NEVER push anything upstream**. All review feedback, analysis, and recommendations must be reported in a review artifact and summarized in the chat.

---

## Workflow Steps

### Step 1: Git Fetch, Checkout, and PR Metadata

When given a PR number `NNNN` (e.g., `review pr 4850`):

1. Check current repository status:
   ```bash
   git status
   ```
2. If there are dirty/uncommitted working tree changes, stash them:
   ```bash
   git stash
   ```
3. Fetch the PR head and checkout `FETCH_HEAD`:
   ```bash
   git fetch origin pull/NNNN/head
   git checkout FETCH_HEAD
   ```
4. Identify the changed file(s) introduced by this PR against `origin/main`:
   ```bash
   git diff --name-only origin/main...HEAD
   ```
   *(Or `git log -p -1` to inspect the latest commit)*.

5. **Fetch PR discussion, reviews, and context from GitHub**:
   Run the helper script to fetch the PR description, top-level reviews, inline comments, and discussions:
   ```bash
   python3 .agents/skills/review-pr/scripts/fetch_pr_info.py NNNN
   ```
   *(Reviewing existing comments reveals author design rationale, prior maintainer/reviewer suggestions, and open items).*

---

### Step 2: Source Paper & Literature Cross-Check

Identify the mathematical source from the module docstring and verify the formalization against ground truth:

1. **arXiv Preprints (`FormalConjectures/Arxiv/YYMM.NNNNN/`)**:
   - Download the arXiv LaTeX source:
     ```bash
     curl -sL -o scratch/YYMM.NNNNN.tar.gz https://arxiv.org/src/YYMM.NNNNN
     mkdir -p scratch/paper && cd scratch/paper && (tar xzf ../YYMM.NNNNN.tar.gz 2>/dev/null || gunzip -c ../YYMM.NNNNN.tar.gz > paper.tex)
     ```
   - Search the LaTeX source for the exact theorem/conjecture/problem number (e.g. `\begin{conjecture}`, `Conjecture 4`, `Problem 7.2`).
   - Check theorem numbering, exact hypotheses, bounds, and constants.

2. **Erdős Problems (`FormalConjectures/ErdosProblems/NNN.lean`)**:
   - Check problem text against `erdosproblems.com/NNN` (e.g., cached in `scratch/problems.yaml` or online).
   - **MANDATORY**: Verify that theorem docstrings include the **verbatim problem text** from `erdosproblems.com` (as required by `FormalConjectures/ErdosProblems/README.md`).

3. **Wikipedia Articles (`FormalConjectures/Wikipedia/`)**:
   - Verify concepts, standard definitions, and historical attributions against the cited Wikipedia page and primary references.

4. **Research Papers / Books / OEIS**:
   - Verify definitions, sequence offsets, and known terms.

---

### Step 3: Mathematical Faithfulness & Degenerate Cases Audit

**CRITICAL: Thoroughly test whether the statement can be trivially proven, disproven, or satisfied in an unintended way!**

1. **Degenerate & Boundary Cases**:
   - **Dimension 0 / Empty / Trivial Spaces**: Check $\dim E = 0$, $n = 0$, $V = \emptyset$, or trivial groups/rings. (E.g., in dimension 0, topological boundaries $\partial K = \operatorname{frontier}(K)$ are empty, which can make statements like $w \in \partial K$ trivially false unless `[Nontrivial E]` or $\dim E \ge 1$ is assumed).
   - **Lattices vs Subgroups**: Check if discrete lattice properties (e.g. full-rank, discrete) are assumed or if arbitrary subgroups collapse/vacuously satisfy hypotheses.
2. **Vacuous or Tautological Statements**:
   - Verify hypotheses are not mutually contradictory (which would make the theorem vacuously true).
   - Check that the conclusion is not an immediate tautology or definitionally equal to an assumption.
3. **Quantification Placement**: For questions using `answer(sorry)`, ensure quantification is placed **after** `answer(sorry)`:
   ```lean
   -- Correct:
   theorem problem_name : answer(sorry) ↔ ∀ n : ℕ, P n := by sorry

   -- Incorrect (rejected):
   theorem problem_name (n : ℕ) : answer(sorry) ↔ P n := by sorry
   ```
4. **Solved vs. Open Status**:
   - Open research problems: `answer(sorry)` and `@[category research open, ...]`.
   - Solved research problems: `answer(True)` or `answer(False)` and `@[category research solved, ...]`.
   - Proved textbook exercises: `@[category textbook, ...]`.
5. **Formal Proof Links**:
   - `@[formal_proof using <kind> at "<link>"]` must point to a genuine formal proof.
   - A `formal_proof` attribute on a `research open` problem triggers a linter error.

---

### Step 4: `FormalConjecturesForMathlib/` Suitability & Separation Audit

**CRITICAL MANDATE: Rigorously evaluate whether every new definition belongs in `FormalConjecturesForMathlib/`!**

Whenever a PR introduces new definitions, structures, predicates, or graph/algebraic/geometric invariants:
1. **Search Mathlib & Existing `FormalConjecturesForMathlib/`**:
   - Check if the concept or standard notation is already defined in Mathlib or `FormalConjecturesForMathlib/` (e.g. `open scoped EuclideanGeometry` for `ℝ²` in `Geometry/2d.lean`, `SimpleGraph.circumference` in `Combinatorics/SimpleGraph/Circumference.lean`, `IsEdgeConnected` in Mathlib).
   - Never allow duplicating notation or concepts that already exist in `FormalConjecturesForMathlib/`.
2. **Identify General / Reusable Mathematical Concepts**:
   - Ask: *Is this definition specific only to this single paper, or is it a standard mathematical concept that other conjectures or Mathlib could use?*
   - Examples of definitions that **MUST be moved to `FormalConjecturesForMathlib/`**:
     - General graph properties (e.g., vertex $k$-connectivity `IsKConnected`, chromatic invariants, independence parameters).
     - Standard algebraic objects (e.g., `WeylAlgebra`, canonical Poisson bracket `poissonBracket`).
     - Geometric definitions (e.g., support functions, convex body properties, Minkowski operations).
     - Combinatorial set family properties (e.g., `PropertyB`).
3. **Strict Quality Rules for `FormalConjecturesForMathlib/`**:
   - **NO `sorry`** is allowed anywhere in `FormalConjecturesForMathlib/`.
   - **NO `native_decide`** is allowed in `FormalConjecturesForMathlib/`.
   - Must include basic API lemmas with full proofs.
   - Must follow Mathlib directory hierarchy and module conventions.

---

### Step 5: Repository Guidelines & Architecture Audit (`AGENTS.md`)

Check all rules defined in `AGENTS.md`:

1. **Copyright Header**: Current year (e.g. `2026`), Apache 2.0 license format.
2. **Imports**:
   - Problem files must import **only `FormalConjecturesUtil`** (unless adding an explicit pointer to another problem or stating an implication).
   - **NO cross-problem imports**: Problem files must never import another problem file (e.g. `import FormalConjectures.ErdosProblems.«602»` or `import FormalConjectures.Wikipedia.Hadamard` is forbidden).
3. **Categories & AMS Classifications**:
   - Every theorem/lemma must have exactly one `@[category ...]` attribute (`research open`, `research solved`, `textbook`, `test`, `API`).
   - `@[category API]` declarations must be **fully proved** (no `sorry`).
   - Every theorem must have at least one `@[AMS ...]` subject classification number (e.g. `AMS 5`, `AMS 11`, `AMS 15`, `AMS 20`).
4. **Naming Conventions**:
   - Theorems/lemmas/Props: `snake_case`.
   - Types, structures, classes, inductive types: `UpperCamelCase`.
   - Functions / terms: `lowerCamelCase`.
5. **Docstrings & LaTeX**:
   - Module docstring must list references with links and short citation keys (e.g. `[AlTa85]`).
   - **MANDATORY LaTeX Formatting**: Mathematical expressions in docstrings must use LaTeX `$ ... $` markdown (e.g., `$K + \Lambda = \mathbb{R}^n$`, `$\partial K$`), not code backticks (`` `...` ``).

---

### Step 6: Lean Compilation Verification

Verify that the formalization compiles without errors or linter warnings:
```bash
lake env lean <path/to/ChangedFile.lean>
```

---

### Step 7: Create Review Artifact and Summary

1. **Create Review Artifact**:
   Write a comprehensive markdown file to the artifact directory:
   `<appDataDir>/brain/<conversation-id>/review_<topic_name>.md`
   containing:
   - Overview & problem description.
   - PR discussion context (author notes, prior reviewer comments).
   - Verification against source literature (with quotes/line numbers from LaTeX or problem DB).
   - **Degenerate cases and mathematical faithfulness assessment**.
   - **`FormalConjecturesForMathlib` suitability and reuse analysis**.
   - Guideline & style compliance checklist table (including LaTeX docstrings).
   - Actionable findings / recommendations with concrete Lean snippets.
   - Clear Verdict: **LGTM (Exemplary)**, **LGTM (High Quality)**, **LGTM with minor suggestions**, or **Changes Requested**.

2. **Present Concise Summary to User**:
   Provide a concise, github-flavored markdown summary highlighting the verdict, key findings, and a clickable link to the review artifact.
