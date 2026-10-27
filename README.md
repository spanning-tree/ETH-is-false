# ETH is false: a checkable statement

OpenAI's Lean proof that the Exponential Time Hypothesis is false
([`openai/math`](https://github.com/openai/math), result 378) is stated in terms of its own machine
model, traces and runtime bounds, which are hard to check. Our goal is a statement you can read in
a few seconds and trust as long as you trust Lean, Mathlib and CSLib: it reuses their definitions
and adds as little as possible of its own, and it is proved from OpenAI's unmodified proof.

Done with the assistance of Claude Opus 5.5 and checked by hand.

## The statement

[`ETHIsFalse/Statement.lean`](ETHIsFalse/Statement.lean) imports only Mathlib and CSLib:

```lean
def SubexponentialThreeSAT : Prop :=
  ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ (n : ℕ) (F : Finset (Finset (Fin n × Bool))), (∀ C ∈ F, C.card ≤ 3) →
        ∃ t ≤ c * (n + F.card + 1) ^ d * 2 ^ (n / r),
        ∃ s ≤ c * (n + F.card + 1) ^ d,
          tm.ComputesInTimeAndSpace (encode n F)
            [decide (∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2)] t s
```

There is a degree `d` such that, for every `r ≥ 1`, a single Turing machine decides satisfiability
of every 3-CNF formula with `n` variables and `m` clauses in at most `c · (n+m+1)^d · 2^(n/r)` steps.
ETH says some `δ > 0` rules out every `2^(δn) · poly` algorithm, so this is its negation.

A formula is a set of clauses, each a set of literals; the literal `(v, b)` means "variable `v`
is `b`". `SubexponentialSharpSAT`, in the same file, is OpenAI's full result: the exact number of
satisfying assignments of `w`-CNF formulas, for every `w`, within the same bounds.

## What it depends on

| from | definitions |
|---|---|
| CSLib `990e65a6` | `Turing.MultiTapeTM` (read-only input tape, `k` work tapes, output tape), `ComputesInTimeAndSpace` (halts within `t` steps with the given output, using `s` work cells) |
| Mathlib `v4.34.1` | `Finset`, `Fin`, `Fintype.card`, `Nat.bits`, … |
| **ours** | `encode`: the input format, `n` in unary, then the sorted clauses, each as the sorted list of its literal numbers `2v+b` in unary (built from `unary`, `frame`, `listCode`, `clauseNumbers`; proved equal to OpenAI's encoding) |
| **ours** | `binary`: the output format of a count, `Nat.bits` with `0 ↦ [false]` (`SubexponentialSharpSAT` only) |

Neither Mathlib nor CSLib defines CNF formulas or an encoding of them, so an input format has to
be fixed here. Nothing of OpenAI's appears in the statement.

## Layout

```
ETHIsFalse/
  Statement.lean        the statements and every definition they use; read this
  Main.lean             theorem eth_is_false, theorem sharpSAT_subexponential
  Proof/
    Bridge.lean         Mathlib formulas ↔ OpenAI's formulas; `encode` = OpenAI's encoding
    Simulation.lean     a CSLib Turing machine simulating OpenAI's machine step for step
    CslibForm.lean      the statements via CSLib's `DecidableInTimeAndSpace`, and their unfolding
    Reduction.lean      OpenAI's theorem ⇒ the statements
    Final.lean          applies the reduction to OpenAI's `exact_count_and_sat`
OpenAI/                 OpenAI's proof, the 3091 files it needs, copied unmodified (Apache-2.0)
```

`OpenAI/OAI/Algorithms/SubexponentialSAT/` is copied from `openai/math` at commit `7ef5c0cc5`
(`lean/OAI/Algorithms/SubexponentialSAT/`); `OpenAI/LICENSE` is its license.

## Build

```sh
lake exe cache get && lake build
```

Lean `v4.34.1`. `Main.lean` prints the axioms: `propext`, `Classical.choice`, `Quot.sound`.
