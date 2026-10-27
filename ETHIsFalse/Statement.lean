import Mathlib
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# The Exponential Time Hypothesis is false: the statement

This is the only file you need to read. It imports only Mathlib and CSLib, and it defines only
what the statements use: how a formula is written on the input tape (`encode`) and, for the
counting statement, how a number is written on the output tape (`binary`).

**Formulas.** A CNF formula with `n` variables is `F : Finset (Finset (Fin n × Bool))`: a set of
clauses, each a set of literals; the literal `(v, b)` says "variable `v` has value `b`". So
`a : Fin n → Bool` satisfies `F` when `∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2`.

**Machines (CSLib).** `Turing.MultiTapeTM k Bool State` is a deterministic Turing machine with a
read-only input tape, `k` work tapes and an output tape, over the alphabet `Bool`.
`tm.ComputesInTimeAndSpace input output t s` says: started on `input`, after `t` steps the machine
has halted with `output` on its output tape, and it has visited `s` work-tape cells.
(This is CSLib's `DecidableInTimeAndSpace` / `ComputableInTimeAndSpace` unfolded; the proof also
derives the statements in that form, see `Proof/CslibForm.lean`.)
-/

namespace ETHIsFalse

/-! ## Input encoding -/

/-- `n` in unary: `n` ones, then a zero. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A bit string made self-delimiting: each bit `b` becomes `true, b`; then a final `false`. -/
def frame (w : List Bool) : List Bool := (w.flatMap fun b => [true, b]) ++ [false]

/-- A list: each element as `true` followed by its framed code; then a final `false`. -/
def listCode {α : Type*} (code : α → List Bool) (as : List α) : List Bool :=
  (as.flatMap fun a => true :: frame (code a)) ++ [false]

/-- A clause as the increasing list of the numbers `2v + b` of its literals `(v, b)`. -/
def clauseNumbers {n : ℕ} (C : Finset (Fin n × Bool)) : List ℕ :=
  (C.image fun l => 2 * l.1.val + l.2.toNat).sort (· ≤ ·)

/-- **The input encoding** of a formula with `n` variables: `n` in unary, then its clauses in
increasing (lexicographic) order, each as the list of its literal numbers in unary. -/
def encode (n : ℕ) (F : Finset (Finset (Fin n × Bool))) : List Bool :=
  unary n ++ listCode (listCode unary) ((F.image clauseNumbers).sort (· ≤ ·))

/-! ## Output encoding (counting statement only) -/

/-- A number in binary, least significant bit first (Mathlib's `Nat.bits`); zero is `[false]`. -/
def binary (a : ℕ) : List Bool := if a = 0 then [false] else a.bits

/-! ## The statements -/

/-- **ETH is false.** There is a degree `d` such that for every `r ≥ 1` one Turing machine decides,
for every 3-CNF formula `F` with `n` variables and `F.card` clauses, whether `F` is satisfiable,
within `c · (n + F.card + 1) ^ d · 2 ^ (n / r)` steps and `c · (n + F.card + 1) ^ d` work cells.

The required output is the one-element list `[decide P]` with
`P := ∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2`. A literal `l = (v, b)` is true under the
assignment `a` when `a v = b`; `P` says that some assignment makes at least one literal of every
clause true. `decide P` is `true` if `P` holds and `false` otherwise (`decide_eq_true_iff`), so the
output is `[true]` if `F` is satisfiable and `[false]` if not. -/
def SubexponentialThreeSAT : Prop :=
  ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ (n : ℕ) (F : Finset (Finset (Fin n × Bool))), (∀ C ∈ F, C.card ≤ 3) →
        ∃ t ≤ c * (n + F.card + 1) ^ d * 2 ^ (n / r),
        ∃ s ≤ c * (n + F.card + 1) ^ d,
          tm.ComputesInTimeAndSpace (encode n F)
            [decide (∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2)] t s

/-- **Exact counting** (OpenAI's actual result). For every clause width `w` there is a degree `d`
such that for every `r ≥ 1` one Turing machine computes, for every `w`-CNF formula `F`, the number
of its satisfying assignments in binary, within the same bounds.

The required output is `binary N` with `N := Fintype.card {a : Fin n → Bool // ...}`, the number
of assignments `a` that make at least one literal of every clause of `F` true. -/
def SubexponentialSharpSAT : Prop :=
  ∀ w : ℕ, ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ (n : ℕ) (F : Finset (Finset (Fin n × Bool))), (∀ C ∈ F, C.card ≤ w) →
        ∃ t ≤ c * (n + F.card + 1) ^ d * 2 ^ (n / r),
        ∃ s ≤ c * (n + F.card + 1) ^ d,
          tm.ComputesInTimeAndSpace (encode n F)
            (binary (Fintype.card {a : Fin n → Bool // ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2})) t s

end ETHIsFalse
