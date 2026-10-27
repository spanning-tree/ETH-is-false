import Mathlib
import Std.Sat.CNF
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# ETH is false

Formulas `Std.Sat.CNF` and satisfiability `F.Sat a` are Lean's. Turing machines
`Turing.MultiTapeTM` and `tm.ComputesInTimeAndSpace input output t s` ("halts within `t` steps
with `output`, having used `s` work cells") are CSLib's. Defined here: the input format `encode`
and the output format `binary`. In the examples, `1` stands for `true` and `0` for `false`.
-/

namespace ETHIsFalse

/-- `n` ones, then a zero. Example: `unary 2 = 110`. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Each bit `b` as `true, b`, then `false`. Example: `frame 10 = 11 10 0`. -/
def frame (w : List Bool) : List Bool := (w.flatMap fun b => [true, b]) ++ [false]

/-- Each element as `true` and its framed code, then `false`.
Example: `listCode unary [0, 1] = 1 frame(0) 1 frame(10) 0 = 1 100 1 11100 0`. -/
def listCode {α : Type*} (code : α → List Bool) (as : List α) : List Bool :=
  (as.flatMap fun a => true :: frame (code a)) ++ [false]

/-- A clause as the sorted list of the numbers `2v + b` of its literals `(v, b)`.
Example: `clauseNumbers {(1, false), (0, true)} = [1, 2]` (`x₀ ↦ 2·0+1`, `¬x₁ ↦ 2·1+0`). -/
def clauseNumbers {n : ℕ} (C : Finset (Fin n × Bool)) : List ℕ :=
  (C.image fun l => 2 * l.1.val + l.2.toNat).sort (· ≤ ·)

/-- The set of clauses of `F`, each as a set of literals (order and repetitions forgotten).
Example: `clauseSet ⟨#[[(0, true)], [(1, false), (0, true)], [(0, true), (0, true)]]⟩`
`= {{(0, true)}, {(0, true), (1, false)}}`. -/
def clauseSet {n : ℕ} (F : Std.Sat.CNF (Fin n)) : Finset (Finset (Fin n × Bool)) :=
  (F.clauses.toList.map List.toFinset).toFinset

/-- **Input**: `n` in unary, then the clauses in sorted order, each as its numbers in unary.
Example: `F = x₀ ∧ (¬x₁ ∨ x₀)` with `n = 2`, that is
`F.clauses = #[[(0, true)], [(1, false), (0, true)]]`:
* `clauseSet F = {{(0, true)}, {(0, true), (1, false)}}`;
* their `clauseNumbers`, sorted: `[[1], [1, 2]]`;
* `encode 2 F = unary 2 ++ listCode (listCode unary) [[1], [1, 2]]`, where
  `listCode unary [1] = 1 11100 0` and `listCode unary [1, 2] = 1 11100 1 1111100 0`. -/
def encode (n : ℕ) (F : Std.Sat.CNF (Fin n)) : List Bool :=
  unary n ++ listCode (listCode unary) (((clauseSet F).image clauseNumbers).sort (· ≤ ·))

/-- **Output** of a count: `Nat.bits` (least significant bit first), zero as `[false]`.
Example: `binary 6 = 011`, `binary 0 = 0`. -/
def binary (a : ℕ) : List Bool := if a = 0 then [false] else a.bits

open Classical in
/-- **ETH is false.** For every `r ≥ 1`, satisfiability of 3-CNF formulas with `n` variables and
`m` clauses is decided in `c · (n + m + 1) ^ d · 2 ^ (n / r)` steps; `d` does not depend on `r`.
The output is `[true]` if `F` is satisfiable, else `[false]`. -/
def SubexponentialThreeSAT : Prop :=
  ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ (n : ℕ) (F : Std.Sat.CNF (Fin n)), (∀ C ∈ F.clauses, C.length ≤ 3) →
        ∃ t ≤ c * (n + F.clauses.size + 1) ^ d * 2 ^ (n / r),
        ∃ s ≤ c * (n + F.clauses.size + 1) ^ d,
          tm.ComputesInTimeAndSpace (encode n F)
            [decide (∃ a : Fin n → Bool, F.Sat a)] t s

open Classical in
/-- **Exact counting.** For every clause width `w`, the number of satisfying assignments of
`w`-CNF formulas is computed within the same bounds. -/
def SubexponentialSharpSAT : Prop :=
  ∀ w : ℕ, ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ (n : ℕ) (F : Std.Sat.CNF (Fin n)), (∀ C ∈ F.clauses, C.length ≤ w) →
        ∃ t ≤ c * (n + F.clauses.size + 1) ^ d * 2 ^ (n / r),
        ∃ s ≤ c * (n + F.clauses.size + 1) ^ d,
          tm.ComputesInTimeAndSpace (encode n F)
            (binary (Fintype.card {a : Fin n → Bool // F.Sat a})) t s

end ETHIsFalse
