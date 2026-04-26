import Mathlib

/-!
# The Variability of Proving 1 + 1 = 2

A comprehensive exploration of proof styles in Lean 4, using the simplest
possible theorem as a laboratory specimen.

## Axes of variation

| Axis          | Left extreme          | Right extreme                    |
|---------------|-----------------------|----------------------------------|
| Style         | term-mode             | tactic-mode                      |
| Automation    | fully manual          | `decide` / `omega` / `norm_num`  |
| Direction     | forward (have/calc)   | backward (apply/rw)              |
| Granularity   | one-liner             | multi-step with helpers          |
| Generality    | concrete `ℕ`          | abstract algebraic structure     |
| Decomposition | monolithic            | many small lemmas                |
| Readability   | terse                 | textbook-style (`calc`/`show`)   |
-/

set_option maxHeartbeats 400000

------------------------------------------------------------------------
-- §1  MAXIMALLY AUTOMATED — "Just let the machine do it"
------------------------------------------------------------------------

/-- The kernel computes both sides and sees they're identical. -/
example : 1 + 1 = 2 := rfl

/-- `decide` asks the kernel to evaluate the decidable proposition. -/
example : 1 + 1 = 2 := by decide

/-- `native_decide` compiles to native code and checks. -/
example : 1 + 1 = 2 := by native_decide

/-- `norm_num` is Mathlib's arithmetic oracle. -/
example : 1 + 1 = 2 := by norm_num

/-- `omega` solves linear arithmetic over ℕ and ℤ. -/
example : 1 + 1 = 2 := by omega

/-- `simp` with the default simp set can close it. -/
example : 1 + 1 = 2 := by simp

/-- `trivial` tries `rfl`, `assumption`, `decide`, etc. -/
example : 1 + 1 = 2 := by trivial

/-- `exact?` would find `rfl`; we can just write that. -/
example : 1 + 1 = 2 := by exact rfl

------------------------------------------------------------------------
-- §2  FULLY MANUAL — Peano-style unfolding
------------------------------------------------------------------------

/-- Explicitly unfold the Peano definitions of `+` on `Nat`.
    `1 = Nat.succ 0`, so `1 + 1 = Nat.succ 0 + Nat.succ 0`.
    By the recursive clause `succ n + m = succ (n + m)`:
      = succ (0 + succ 0)
    By the base clause `0 + n = n`:
      = succ (succ 0) = 2`. -/
example : 1 + 1 = 2 := by
  show Nat.succ 0 + Nat.succ 0 = 2
  rw [Nat.succ_add, Nat.zero_add]

/-- Same argument, but with `unfold` to peel away the typeclass layers. -/
example : 1 + 1 = 2 := by
  unfold HAdd.hAdd instHAdd Add.add Nat.add
  rfl

/-- Pure rewriting, step by step. -/
example : 1 + 1 = 2 := by
  show Nat.succ 0 + Nat.succ 0 = 2
  rw [Nat.succ_add]          -- closes after reduction

------------------------------------------------------------------------
-- §3  TERM-MODE proofs
------------------------------------------------------------------------

/-- Direct definitional equality — the simplest proof term. -/
example : 1 + 1 = 2 := Eq.refl 2

/-- Fully explicit: `@rfl Nat 2` spells out the universe and type. -/
example : 1 + 1 = 2 := @rfl Nat 2

/-- Using `show` to make the type annotation explicit. -/
example : 1 + 1 = 2 := show 2 = 2 from rfl

/-- Using `id` — a slightly more obfuscated rfl. -/
example : 1 + 1 = 2 := id rfl

/-- Congruence: apply `· + 1` to `rfl : 1 = 1`. -/
example : 1 + 1 = 2 := congrArg (· + 1) (rfl : 1 = 1)

------------------------------------------------------------------------
-- §4  CALC-STYLE — textbook readability
------------------------------------------------------------------------

/-- A `calc` block that mirrors a textbook derivation. -/
example : 1 + 1 = 2 :=
  calc 1 + 1
      = Nat.succ 0 + Nat.succ 0     := rfl
    _ = Nat.succ (0 + Nat.succ 0)   := by rw [Nat.succ_add]
    _ = Nat.succ (Nat.succ 0)       := by rw [Nat.zero_add]
    _ = 2                            := rfl

/-- A shorter `calc` proof. -/
example : 1 + 1 = 2 :=
  calc 1 + 1 = 2 := by norm_num

------------------------------------------------------------------------
-- §5  ALGEBRAIC / ABSTRACT — lifting to general structures
------------------------------------------------------------------------

/-- In any `AddMonoidWithOne` the statement is a consequence of
    how `2` is *defined* as `1 + 1`. -/
example {M : Type*} [AddMonoidWithOne M] : (1 : M) + 1 = (2 : M) :=
  one_add_one_eq_two

/-- Specialised to ℕ via the same lemma. -/
example : (1 : ℕ) + 1 = 2 := one_add_one_eq_two

/-- Via `Fin 3` — modular arithmetic, but 1+1 < 3 so no wrap-around. -/
example : (1 : Fin 3) + 1 = 2 := by decide

/-- In ℤ. -/
example : (1 : ℤ) + 1 = 2 := by norm_num

/-- In ℚ. -/
example : (1 : ℚ) + 1 = 2 := by norm_num

/-- In ℝ. -/
example : (1 : ℝ) + 1 = 2 := by norm_num

/-- In ℂ. -/
example : (1 : ℂ) + 1 = 2 := by norm_num

/-- In `ZMod 5` (so 1 + 1 ≡ 2 mod 5). -/
example : (1 : ZMod 5) + 1 = 2 := by decide

/-- Via `nsmul`: `2 • 1 = 2`. -/
example : 2 • (1 : ℕ) = 2 := by norm_num

/-- `ring` works because ℕ is a semiring. -/
example : 1 + 1 = 2 := by ring

------------------------------------------------------------------------
-- §6  TYPE THEORY — Curry–Howard and proof irrelevance
------------------------------------------------------------------------

/-- The proof is a term of type `1 + 1 = 2`; `rfl` is the canonical
    inhabitant of `@Eq Nat 2 2` (after reduction). -/
example : 1 + 1 = 2 := @rfl Nat 2

/-- We can build the proof via `Eq.mpr` and a definitional cast. -/
example : 1 + 1 = 2 :=
  Eq.mpr (id (congrArg (· = 2) rfl)) rfl

/-- Using proof irrelevance: any two proofs of `1+1=2` are equal. -/
example (h₁ h₂ : 1 + 1 = 2) : h₁ = h₂ := rfl  -- proof irrelevance

/-- Heterogeneous equality via `HEq.refl`. -/
example : HEq (1 + 1) 2 := HEq.refl 2

------------------------------------------------------------------------
-- §7  CATEGORY THEORY — morphisms in concrete categories
------------------------------------------------------------------------

/-- In the category `Type`, the coproduct `Unit ⊕ Unit` has exactly
    two elements — a categorical encoding of `1 + 1 = 2`. -/
example : Fintype.card (Unit ⊕ Unit) = 2 := by decide

open CategoryTheory in
/-- The statement `1 + 1 = 2` in the *endomorphism monoid*:
    composing the identity with itself gives the identity. -/
example : (CategoryStruct.comp (𝟙 Unit) (𝟙 Unit)) = 𝟙 Unit := by
  simp

/-- In `ℕ` viewed as a discrete category, `1 + 1 = 2` is just
    equality of objects — definitional. -/
example : (1 : ℕ) + 1 = 2 := rfl

------------------------------------------------------------------------
-- §8  LOGIC / SET THEORY flavour
------------------------------------------------------------------------

/-- Via cardinality: `|{0}| + |{1}| = |{0,1}|` as `Finset.card`. -/
example : ({0} : Finset ℕ).card + ({1} : Finset ℕ).card =
          ({0, 1} : Finset ℕ).card := by decide

/-- `Fin` cardinality: `Fin 1 ⊕ Fin 1 ≃ Fin 2`. -/
example : Fintype.card (Fin 1 ⊕ Fin 1) = 2 := by decide

/-- Via `Cardinal`: `1 + 1 = 2` in the world of cardinal arithmetic. -/
example : (1 : Cardinal) + 1 = 2 := by norm_num

------------------------------------------------------------------------
-- §9  MORE TACTIC STYLES
------------------------------------------------------------------------

-- `first` combinator — try `rfl`, fall back to `norm_num`.
-- (Here `rfl` succeeds, so `norm_num` is never reached — but on harder
-- goals only the fallback would fire.)
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
example : 1 + 1 = 2 := by
  first | rfl | norm_num

/-- Using `change` to assert definitional equality. -/
example : 1 + 1 = 2 := by
  change 2 = 2
  rfl

/-- Using `show`. -/
example : 1 + 1 = 2 := by
  show 2 = 2
  rfl

/-- Using `suffices`. -/
example : 1 + 1 = 2 := by
  suffices h : 2 = 2 from h
  rfl

/-- A `have`-chain forward proof. -/
example : 1 + 1 = 2 := by
  have h₁ : 0 + 1 = 1 := Nat.zero_add 1
  have h₂ : Nat.succ 0 + 1 = Nat.succ (0 + 1) := Nat.succ_add 0 1
  have h₃ : Nat.succ (0 + 1) = Nat.succ 1 := congrArg Nat.succ h₁
  exact h₂.trans h₃

------------------------------------------------------------------------
-- §10  DECOMPOSED INTO HELPER LEMMAS
------------------------------------------------------------------------

private lemma zero_add_one : 0 + 1 = 1 := Nat.zero_add 1

private lemma succ_zero_eq_one : Nat.succ 0 = 1 := rfl

private lemma succ_add_one : Nat.succ 0 + 1 = Nat.succ (0 + 1) :=
  Nat.succ_add 0 1

theorem one_plus_one_decomposed : 1 + 1 = 2 := by
  calc  1 + 1
      = Nat.succ 0 + 1   := by rw [← succ_zero_eq_one]
    _ = Nat.succ (0 + 1)  := succ_add_one
    _ = Nat.succ 1        := by rw [zero_add_one]
    _ = 2                  := rfl

------------------------------------------------------------------------
-- §11  THE "WRONG WAY ROUND" — symmetry
------------------------------------------------------------------------

example : 1 + 1 = 2 := by
  symm
  show 2 = 1 + 1
  rfl

example : 1 + 1 = 2 := Eq.symm (rfl : (2 : ℕ) = 2)

------------------------------------------------------------------------
-- §12  META / ELABORATION TRICKS
------------------------------------------------------------------------

/-- `Decidable.decide` builds the proof via kernel reduction. -/
example : 1 + 1 = 2 := of_decide_eq_true (Eq.refl true)

/-- Via `Nat.eq_of_le_of_lt_succ` + `omega`. -/
example : 1 + 1 = 2 := by
  apply Nat.eq_of_le_of_lt_succ <;> omega

------------------------------------------------------------------------
-- SUMMARY
------------------------------------------------------------------------

/-!
## Key takeaways

1. **`rfl`** is king for definitionally-equal terms — it is the
   simplest, fastest, and most robust proof.

2. **Automation tactics** (`decide`, `omega`, `norm_num`, `simp`, `ring`)
   each use a different internal algorithm; they all solve `1+1=2` but
   diverge dramatically on harder problems.

3. **Term-mode** proofs (`rfl`, `Eq.refl 2`, `congrArg …`) expose the
   Curry–Howard correspondence directly.

4. **`calc` blocks** are the sweet spot for readable, step-by-step proofs
   that still have full machine verification.

5. **Algebraic generality** lets you prove `1 + 1 = 2` once for *every*
   `AddMonoidWithOne` — illustrating the power of typeclasses.

6. **Category-theoretic** encodings are possible but somewhat forced for
   this particular statement, since `1+1=2` is inherently about additive
   structure, not composition.  The most natural categorical version is
   the cardinality statement `|Unit ⊕ Unit| = 2`.

7. **Proof irrelevance** (`h₁ = h₂ : rfl`) reminds us that in Lean's
   type theory, *how* you prove a Prop doesn't matter — only *that*
   you prove it.

8. The "proof design space" axes (style, automation, direction,
   granularity, generality, decomposition, readability) are genuinely
   independent — you can mix and match freely.
-/
