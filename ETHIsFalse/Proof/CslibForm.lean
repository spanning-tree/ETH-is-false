import ETHIsFalse.Statement
import ETHIsFalse.Proof.Bridge
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds

/-!
# The statements in CSLib's vocabulary

`SubexponentialThreeSATCslib` and `SubexponentialSharpSATCslib` say the same as `SubexponentialThreeSAT` and `SubexponentialSharpSAT`
with CSLib's `DecidableInTimeAndSpace` and `ComputableInTimeAndSpace`, which take the encodings as
embeddings `↪ List Bool`. `subexponentialThreeSAT_of_cslib` and `subexponentialSharpSAT_of_cslib` unfold them.
-/

namespace ETHIsFalse.Proof

/-- `k`-CNF formulas. -/
abbrev KCNF (k : ℕ) := Σ n : ℕ, {F : Finset (Finset (Fin n × Bool)) // ∀ C ∈ F, C.card ≤ k}

/-- `encodeSet` as an embedding of `k`-CNF formulas (as sets of sets of literals). -/
def encodeK (k : ℕ) : KCNF k ↪ List Bool :=
  ⟨fun F => encodeSet F.1 F.2.1, fun F G h => by
    obtain ⟨n, F, hF⟩ := F
    obtain ⟨m, G, hG⟩ := G
    have key : (⟨n, F⟩ : Σ n, CNF n) = ⟨m, G⟩ := encode_injective h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp key
    cases eq_of_heq h
    rfl⟩

/-- 3-CNF formulas. -/
abbrev ThreeCNF := KCNF 3

/-- `encodeSet` as an embedding of 3-CNF formulas. -/
abbrev encode3 : ThreeCNF ↪ List Bool := encodeK 3

/-- `binary` as an embedding. -/
def binaryEmb : ℕ ↪ List Bool :=
  ⟨binary, fun a b h => by
    have h' : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord a =
        OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord b := h
    simpa using congrArg OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat h'⟩

/-- `SubexponentialThreeSAT` with CSLib's `DecidableInTimeAndSpace`. -/
def SubexponentialThreeSATCslib : Prop :=
  ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    Turing.MultiTapeTM.DecidableInTimeAndSpace
      {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2}
      encode3
      (fun F => c * (F.1 + F.2.1.card + 1) ^ d * 2 ^ (F.1 / r))
      (fun F => c * (F.1 + F.2.1.card + 1) ^ d)

/-- `SubexponentialSharpSAT` with CSLib's `ComputableInTimeAndSpace`. -/
def SubexponentialSharpSATCslib : Prop :=
  ∀ k : ℕ, ∃ d : ℕ, ∀ r : ℕ, 0 < r → ∃ c : ℕ,
    Turing.MultiTapeTM.ComputableInTimeAndSpace
      (fun F : KCNF k => Fintype.card {a : Fin F.1 → Bool // ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2})
      (encodeK k) binaryEmb
      (fun F => c * (F.1 + F.2.1.card + 1) ^ d * 2 ^ (F.1 / r))
      (fun F => c * (F.1 + F.2.1.card + 1) ^ d)

/-! ### From Lean's `Std.Sat.CNF` to sets of clauses -/

theorem card_clauseSet_le {n : ℕ} (F : Std.Sat.CNF (Fin n)) :
    (clauseSet F).card ≤ F.clauses.size := by
  unfold clauseSet
  calc _ ≤ (F.clauses.toList.map List.toFinset).length := List.toFinset_card_le _
    _ = F.clauses.size := by simp

theorem width_clauseSet {n w : ℕ} {F : Std.Sat.CNF (Fin n)} (h : ∀ C ∈ F.clauses, C.length ≤ w) :
    ∀ C ∈ clauseSet F, C.card ≤ w := by
  intro C hC
  simp only [clauseSet, List.mem_toFinset, List.mem_map, Array.mem_toList_iff] at hC
  obtain ⟨c, hc, rfl⟩ := hC
  exact (List.toFinset_card_le c).trans (h c hc)

theorem sat_iff {n : ℕ} (F : Std.Sat.CNF (Fin n)) (a : Fin n → Bool) :
    F.Sat a ↔ ∀ C ∈ clauseSet F, ∃ l ∈ C, a l.1 = l.2 := by
  simp only [Std.Sat.CNF.Sat, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval, clauseSet]
  simp
  constructor
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
    exact h i hi
  · intro h i hi
    exact h _ (Array.getElem_mem hi)

/-! ### Unfolding -/

open Classical in
theorem subexponentialThreeSAT_of_cslib (h : SubexponentialThreeSATCslib) :
    SubexponentialThreeSAT := by
  unfold SubexponentialThreeSATCslib Turing.MultiTapeTM.DecidableInTimeAndSpace
    Turing.MultiTapeTM.ComputableInTimeAndSpace Turing.MultiTapeTM.ComputesFunInTimeAndSpace at h
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun r hr => ?_⟩
  obtain ⟨c, k, State, hfin, tm, htm⟩ := hd r hr
  refine ⟨c, k, State, hfin, tm, fun n F hF => ?_⟩
  obtain ⟨t, ht, s, hs, hc⟩ := htm ⟨n, clauseSet F, width_clauseSet hF⟩
  have hm := card_clauseSet_le F
  have key : (⟨n, clauseSet F, width_clauseSet hF⟩ : ThreeCNF) ∈
      {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2} ↔
      ∃ a : Fin n → Bool, F.Sat a :=
    (exists_congr fun a => sat_iff F a).symm
  have hb : Turing.MultiTapeTM.indicator
      {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2}
      ⟨n, clauseSet F, width_clauseSet hF⟩ = decide (∃ a : Fin n → Bool, F.Sat a) := by
    unfold Turing.MultiTapeTM.indicator
    by_cases hsat : ∃ a : Fin n → Bool, F.Sat a
    · rw [if_pos (key.mpr hsat), decide_eq_true hsat]
    · rw [if_neg (fun hm => hsat (key.mp hm)), decide_eq_false hsat]
  rw [hb] at hc
  refine ⟨t, ht.trans ?_, s, hs.trans ?_, hc⟩
  · show c * (n + (clauseSet F).card + 1) ^ d * 2 ^ (n / r) ≤
      c * (n + F.clauses.size + 1) ^ d * 2 ^ (n / r)
    gcongr
  · show c * (n + (clauseSet F).card + 1) ^ d ≤ c * (n + F.clauses.size + 1) ^ d
    gcongr

open Classical in
theorem subexponentialSharpSAT_of_cslib (h : SubexponentialSharpSATCslib) :
    SubexponentialSharpSAT := by
  unfold SubexponentialSharpSATCslib Turing.MultiTapeTM.ComputableInTimeAndSpace
    Turing.MultiTapeTM.ComputesFunInTimeAndSpace at h
  intro w
  obtain ⟨d, hd⟩ := h w
  refine ⟨d, fun r hr => ?_⟩
  obtain ⟨c, k, State, hfin, tm, htm⟩ := hd r hr
  refine ⟨c, k, State, hfin, tm, fun n F hF => ?_⟩
  obtain ⟨t, ht, s, hs, hc⟩ := htm ⟨n, clauseSet F, width_clauseSet hF⟩
  have hm := card_clauseSet_le F
  have hcard : Fintype.card {a : Fin n → Bool // F.Sat a} =
      Fintype.card {a : Fin n → Bool // ∀ C ∈ clauseSet F, ∃ l ∈ C, a l.1 = l.2} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun a => sat_iff F a)
  refine ⟨t, ht.trans ?_, s, hs.trans ?_, ?_⟩
  · show c * (n + (clauseSet F).card + 1) ^ d * 2 ^ (n / r) ≤
      c * (n + F.clauses.size + 1) ^ d * 2 ^ (n / r)
    gcongr
  · show c * (n + (clauseSet F).card + 1) ^ d ≤ c * (n + F.clauses.size + 1) ^ d
    gcongr
  · rw [hcard]
    exact hc

end ETHIsFalse.Proof
