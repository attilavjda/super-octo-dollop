# Summary of changes for run d16ea992-94e6-4af4-9495-f76b4aef0392
I've created a comprehensive guide at `ProofWritingGuide.md` covering your questions in depth. Here's a summary of what's inside:

## What the guide covers:

**1. Three Fundamental Proof Styles** — Tactic mode (`by ...`), term mode (direct proof expressions), and structured/calculus style (`calc`, `have`, `show`). These are freely mixable in Lean 4.

**2. Ten+ Approaches to Writing Any Proof** — Direct proof, rewriting, case analysis, induction, contradiction, contrapositive, forward reasoning, backward reasoning, construction/witness, and calculation chains — each with when to use them and which tactics to reach for.

**3. How to Know Which Approach to Use** — A decision tree based on the *shape of the goal* (`∀`, `∃`, `∧`, `∨`, `↔`, `=`, `≤`, etc.) and the *hypotheses available*.

**4. Tweakable Aspects (Adding Variability)** — Seven independent axes you can vary in any proof: granularity, automation level, named vs. anonymous hypotheses, forward vs. backward reasoning, choice of library lemma, decomposition into helpers, and type generality.

**5. Twelve Tiny Patterns for New Learners** — Self-contained mini-exercises covering `rfl`, `intro`/`exact`, `constructor`, `cases`, `use`, `induction`, `calc`, `simp`, `omega`, `by_contra`, style-switching, and discovery tactics (`exact?`, `simp?`, `apply?`).

**6. Resources** — Mathematics in Lean (best tutorial for mathematicians), Natural Number Game (best starting point for complete beginners), Theorem Proving in Lean 4, Lean Zulip chat, Mathlib docs, and more.

**7. A Mental Framework** — Think of the "proof design space" as having independent axes (style, automation, direction, granularity, generality, decomposition, readability). Deliberately rewriting proofs along each axis is the fastest way to build intuition.

**8. Quick Reference Tactic Cheat Sheet** — A table of ~25 commonly used tactics with one-line descriptions.