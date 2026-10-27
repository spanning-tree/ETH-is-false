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

/-- `encode` as an embedding of `k`-CNF formulas. -/
def encodeK (k : ℕ) : KCNF k ↪ List Bool :=
  ⟨fun F => encode F.1 F.2.1, fun F G h => by
    obtain ⟨n, F, hF⟩ := F
    obtain ⟨m, G, hG⟩ := G
    have key : (⟨n, F⟩ : Σ n, CNF n) = ⟨m, G⟩ := encode_injective h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp key
    cases eq_of_heq h
    rfl⟩

/-- 3-CNF formulas. -/
abbrev ThreeCNF := KCNF 3

/-- `encode` as an embedding of 3-CNF formulas. -/
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

theorem subexponentialThreeSAT_of_cslib (h : SubexponentialThreeSATCslib) :
    SubexponentialThreeSAT := by
  unfold SubexponentialThreeSATCslib Turing.MultiTapeTM.DecidableInTimeAndSpace
    Turing.MultiTapeTM.ComputableInTimeAndSpace Turing.MultiTapeTM.ComputesFunInTimeAndSpace at h
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun r hr => ?_⟩
  obtain ⟨c, k, State, hfin, tm, htm⟩ := hd r hr
  refine ⟨c, k, State, hfin, tm, fun n F hF => ?_⟩
  obtain ⟨t, ht, s, hs, hc⟩ := htm ⟨n, F, hF⟩
  have key : (⟨n, F, hF⟩ : ThreeCNF) ∈
      {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2} ↔
      ∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2 := Iff.rfl
  have hb : Turing.MultiTapeTM.indicator
      {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2} ⟨n, F, hF⟩ =
      decide (∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2) := by
    unfold Turing.MultiTapeTM.indicator
    by_cases hsat : ∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2
    · rw [if_pos (key.mpr hsat), decide_eq_true hsat]
    · rw [if_neg (fun hm => hsat (key.mp hm)), decide_eq_false hsat]
  rw [hb] at hc
  exact ⟨t, ht, s, hs, hc⟩

theorem subexponentialSharpSAT_of_cslib (h : SubexponentialSharpSATCslib) :
    SubexponentialSharpSAT := by
  unfold SubexponentialSharpSATCslib Turing.MultiTapeTM.ComputableInTimeAndSpace
    Turing.MultiTapeTM.ComputesFunInTimeAndSpace at h
  intro w
  obtain ⟨d, hd⟩ := h w
  refine ⟨d, fun r hr => ?_⟩
  obtain ⟨c, k, State, hfin, tm, htm⟩ := hd r hr
  refine ⟨c, k, State, hfin, tm, fun n F hF => ?_⟩
  obtain ⟨t, ht, s, hs, hc⟩ := htm ⟨n, F, hF⟩
  exact ⟨t, ht, s, hs, hc⟩

end ETHIsFalse.Proof
