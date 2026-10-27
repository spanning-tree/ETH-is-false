import ETHIsFalse.Proof.CslibForm
import ETHIsFalse.Proof.Simulation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

/-!
# From OpenAI's comparator theorem to the statements in CSLib's vocabulary

`OAIStatement k` is, word for word, the statement of
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat k` (the theorem of
`lean/ComparatorChallenges/SubexponentialSAT.lean`). `ethIsFalse_of` derives `SubexponentialThreeSATCslib` from
its case `k = 3`; `countingIsSubexponential_of` derives `SubexponentialSharpSATCslib` from all `k ≥ 2`.
-/

namespace ETHIsFalse.Proof

open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace Filter Topology

/-- The statement of OpenAI's `SqrtLogSpace.exact_count_and_sat k`. -/
def OAIStatement (k : ℕ) : Prop :=
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape answerTape : Fin machine.tapeCount)
      (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF F)) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes answerTape =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF F)) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e

/-- `(log log x)² / √(log x)` tends to zero. -/
theorem tendsto_scale_ratio :
    Tendsto (fun n : ℕ => (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
      Real.sqrt (Real.log ((n : ℝ) + 16))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y ^ (2 : ℝ) / y ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h1' : Tendsto (fun y : ℝ => Real.log y ^ 2 / Real.sqrt y) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.sqrt_eq_rpow, Real.rpow_two]
  have h2 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 16 tendsto_natCast_atTop_atTop)
  exact h1'.comp h2

/-- `A · runtimeScale n ≤ n / r + c₀` for a constant `c₀`. -/
theorem scale_le (A : ℝ) (r : ℕ) (hr : 0 < r) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ n : ℕ,
      A * SqrtLog.Statement.runtimeScale n ≤ (n : ℝ) / r + c₀ := by
  have hr' : (0 : ℝ) < 1 / ((r : ℝ) * (|A| + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 tendsto_scale_ratio).2 _ hr')
  refine ⟨∑ n ∈ Finset.range N, |A * SqrtLog.Statement.runtimeScale n|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hg := hN n hn
    have hgnn : 0 ≤ (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
        Real.sqrt (Real.log ((n : ℝ) + 16)) := by positivity
    have hscale : SqrtLog.Statement.runtimeScale n = (n : ℝ) *
        ((Real.log (Real.log ((n : ℝ) + 16))) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16))) := by
      unfold SqrtLog.Statement.runtimeScale; ring
    have hsum : 0 ≤ ∑ n ∈ Finset.range N, |A * SqrtLog.Statement.runtimeScale n| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hscale]
    have hA : A * ((Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
        Real.sqrt (Real.log ((n : ℝ) + 16))) ≤ 1 / r := by
      calc _ ≤ |A| * ((Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
            Real.sqrt (Real.log ((n : ℝ) + 16))) :=
            mul_le_mul_of_nonneg_right (le_abs_self A) hgnn
        _ ≤ (|A| + 1) * (1 / ((r : ℝ) * (|A| + 1))) := by
            apply mul_le_mul (by linarith) hg.le hgnn (by positivity)
        _ = 1 / r := by field_simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc A * ((n : ℝ) * _) = (n : ℝ) * (A * ((Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
          Real.sqrt (Real.log ((n : ℝ) + 16)))) := by ring
      _ ≤ (n : ℝ) * (1 / r) := mul_le_mul_of_nonneg_left hA hn0
      _ ≤ (n : ℝ) / r + _ := by rw [mul_one_div]; linarith
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have h1 := Finset.single_le_sum (f := fun n => |A * SqrtLog.Statement.runtimeScale n|)
      (fun _ _ => abs_nonneg _) hmem
    have h2 : (0 : ℝ) ≤ (n : ℝ) / r := by positivity
    have h3 := le_abs_self (A * SqrtLog.Statement.runtimeScale n)
    linarith

/-- `2 ^ (n / r)` over the reals is at most twice `2 ^ (n / r)` with natural division. -/
theorem rpow_div_le (n r : ℕ) (hr : 0 < r) :
    (2 : ℝ) ^ ((n : ℝ) / r) ≤ 2 * (2 : ℝ) ^ (n / r) := by
  have hfloor : (n : ℝ) / r ≤ ((n / r : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((n : ℝ) / r)
    rw [Nat.floor_div_eq_div] at this
    linarith
  calc (2 : ℝ) ^ ((n : ℝ) / r) ≤ (2 : ℝ) ^ (((n / r : ℕ) : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
    _ = 2 * (2 : ℝ) ^ (n / r) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]; ring

theorem indicator_eq (F : ThreeCNF) :
    Turing.MultiTapeTM.indicator
      {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2} F =
      decide (0 < SAT.count (toOAI F.2.1)) := by
  have key : F ∈ {F : ThreeCNF | ∃ a : Fin F.1 → Bool, ∀ C ∈ F.2.1, ∃ l ∈ C, a l.1 = l.2} ↔
      0 < SAT.count (toOAI F.2.1) := by
    rw [SAT.count_pos_iff, satisfiable_toOAI]; exact Iff.rfl
  unfold Turing.MultiTapeTM.indicator
  by_cases h : 0 < SAT.count (toOAI F.2.1)
  · rw [if_pos (key.mpr h), decide_eq_true h]
  · rw [if_neg (fun hm => h (key.mp hm)), decide_eq_false h]

/-- **The reduction.** OpenAI's theorem for width three gives the clean statement. -/
theorem ethIsFalse_of (h : OAIStatement 3) : SubexponentialThreeSATCslib := by
  unfold OAIStatement at h
  obtain ⟨M, _countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hM⟩ := h
  unfold SubexponentialThreeSATCslib
  let D := 2 * d + 2 * e + 2
  refine ⟨D, fun r hr => ?_⟩
  obtain ⟨c₀, hc₀, hscale⟩ := scale_le A r hr
  let K : ℝ := C * 31 ^ d * 2 ^ (c₀ + 1)
  let c : ℕ := ⌈K⌉₊ + 62 + ⌈S * 31 ^ e⌉₊ + 32 * M.tapeCount
  refine ⟨c, ?_⟩
  unfold Turing.MultiTapeTM.DecidableInTimeAndSpace Turing.MultiTapeTM.ComputableInTimeAndSpace
    Turing.MultiTapeTM.ComputesFunInTimeAndSpace
  refine ⟨M.tapeCount, Sim.St M, inferInstance, Sim.tm M none, fun F => ?_⟩
  obtain ⟨n, G, hw⟩ := F
  obtain ⟨time, final, htr, -, -, hstate, -, -, htime, hspace⟩ :=
    hM n (toOAI G) (widthAtMost_toOAI hw)
  have hinput : encode3 ⟨n, G, hw⟩ = Encoding.encodeCNF (toOAI G) := encode_eq G
  have hL : (encode3 ⟨n, G, hw⟩).length = Encoding.formulaBitLength (toOAI G) := by
    rw [hinput]; rfl
  rw [← hinput] at htr
  obtain ⟨hcomp, hsp⟩ := Sim.simulate M htr hstate
  rw [hL] at hcomp hsp
  set L := Encoding.formulaBitLength (toOAI G) with hLdef
  set N := n + G.card + 1 with hN
  have h31 : ((8 * 3 + 7 : ℕ) : ℝ) = 31 := by norm_num
  have hsize : L + 1 ≤ 31 * N ^ 2 := by
    have := encoding_le_declaredSize_sq (toOAI G) (widthAtMost_toOAI hw)
    rw [card_toOAI, ← hLdef, ← hN] at this
    omega
  have hsizeR : ((L : ℝ) + 1) ^ d ≤ 31 ^ d * (N : ℝ) ^ (2 * d) := by
    have := encoding_pow_le_declaredSize (toOAI G) (widthAtMost_toOAI hw) d
    rw [card_toOAI, ← hLdef, ← hN, h31] at this
    exact this
  have hsizeR' : ((L : ℝ) + 1) ^ e ≤ 31 ^ e * (N : ℝ) ^ (2 * e) := by
    have := encoding_pow_le_declaredSize (toOAI G) (widthAtMost_toOAI hw) e
    rw [card_toOAI, ← hLdef, ← hN, h31] at this
    exact this
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpow : ∀ a ≤ D, (N : ℝ) ^ a ≤ (N : ℝ) ^ D := fun a ha => pow_le_pow_right₀ hN1R ha
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (n / r) := one_le_pow₀ (by norm_num)
  refine ⟨2 * L + 2 + time, ?_,
    (Sim.tm M none).spaceUsed ((Sim.tm M none).initCfg (encode3 ⟨n, G, hw⟩)) (2 * L + 2 + time), ?_, ?_⟩
  · -- time
    have hT : (time : ℝ) ≤ K * (N : ℝ) ^ (2 * d) * (2 : ℝ) ^ (n / r) := by
      have h2 : (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤
          2 ^ (c₀ + 1) * (2 : ℝ) ^ (n / r) := by
        calc (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n)
            ≤ (2 : ℝ) ^ ((n : ℝ) / r + c₀) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (hscale n)
          _ = 2 ^ c₀ * (2 : ℝ) ^ ((n : ℝ) / r) := by
              rw [Real.rpow_add (by norm_num)]; ring
          _ ≤ 2 ^ c₀ * (2 * (2 : ℝ) ^ (n / r)) :=
              mul_le_mul_of_nonneg_left (rpow_div_le n r hr) (by positivity)
          _ = 2 ^ (c₀ + 1) * (2 : ℝ) ^ (n / r) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
      calc (time : ℝ) ≤ C * ((L : ℝ) + 1) ^ d * 2 ^ (A * SqrtLog.Statement.runtimeScale n) :=
            htime
        _ ≤ C * (31 ^ d * (N : ℝ) ^ (2 * d)) * (2 ^ (c₀ + 1) * (2 : ℝ) ^ (n / r)) := by
            gcongr
        _ = K * (N : ℝ) ^ (2 * d) * (2 : ℝ) ^ (n / r) := by ring
    have hTot : ((2 * L + 2 + time : ℕ) : ℝ) ≤ (c : ℝ) * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by
      have hLR : (2 * (L : ℝ) + 2) ≤ 62 * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by
        have : ((L : ℝ) + 1) ≤ 31 * (N : ℝ) ^ 2 := by exact_mod_cast hsize
        have h2D := hpow 2 (by omega)
        have hND : (0 : ℝ) ≤ (N : ℝ) ^ D := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpow2 hND]
      have hK : K * (N : ℝ) ^ (2 * d) * (2 : ℝ) ^ (n / r) ≤
          (⌈K⌉₊ : ℝ) * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by
        have := hpow (2 * d) (by omega)
        have hKc := Nat.le_ceil K
        have hK0 : 0 ≤ K := by positivity
        gcongr
      have hc : (c : ℝ) = ⌈K⌉₊ + 62 + ⌈S * 31 ^ e⌉₊ + 32 * M.tapeCount := by
        simp [c]
      have hrest : (0 : ℝ) ≤ ((⌈S * 31 ^ e⌉₊ : ℝ) + 32 * M.tapeCount) *
          (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by positivity
      push_cast
      rw [hc]
      nlinarith
    show 2 * L + 2 + time ≤ c * N ^ D * 2 ^ (n / r)
    exact_mod_cast hTot
  · -- space
    have hS' : (visitedSpace final : ℝ) ≤ S * ((L : ℝ) + 1) ^ e := hspace time final le_rfl (by rwa [hinput] at htr)
    have hSp : ((Sim.tm M none).spaceUsed ((Sim.tm M none).initCfg (encode3 ⟨n, G, hw⟩))
        (2 * L + 2 + time) : ℝ) ≤ (c : ℝ) * (N : ℝ) ^ D := by
      have h1 : ((Sim.tm M none).spaceUsed ((Sim.tm M none).initCfg (encode3 ⟨n, G, hw⟩))
          (2 * L + 2 + time) : ℝ) ≤ visitedSpace final + M.tapeCount * ((L : ℝ) + 2) := by
        exact_mod_cast hsp
      have h2 : S * ((L : ℝ) + 1) ^ e ≤ ⌈S * 31 ^ e⌉₊ * (N : ℝ) ^ D := by
        calc S * ((L : ℝ) + 1) ^ e ≤ S * (31 ^ e * (N : ℝ) ^ (2 * e)) := by gcongr
          _ = (S * 31 ^ e) * (N : ℝ) ^ (2 * e) := by ring
          _ ≤ ⌈S * 31 ^ e⌉₊ * (N : ℝ) ^ D := by
              gcongr
              · exact Nat.le_ceil _
              · omega
      have h3 : (M.tapeCount : ℝ) * ((L : ℝ) + 2) ≤ 32 * M.tapeCount * (N : ℝ) ^ D := by
        have : ((L : ℝ) + 1) ≤ 31 * (N : ℝ) ^ 2 := by exact_mod_cast hsize
        have h2D := hpow 2 (by omega)
        have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1R
        have hk : (0 : ℝ) ≤ M.tapeCount := Nat.cast_nonneg _
        nlinarith
      have hc : (c : ℝ) = ⌈K⌉₊ + 62 + ⌈S * 31 ^ e⌉₊ + 32 * M.tapeCount := by
        simp [c]
      have hrest : (0 : ℝ) ≤ ((⌈K⌉₊ : ℝ) + 62) * (N : ℝ) ^ D := by positivity
      rw [hc]
      nlinarith
    show _ ≤ c * N ^ D
    exact_mod_cast hSp
  · -- correctness
    simp only [Function.Embedding.coeFn_mk]
    rw [indicator_eq ⟨n, G, hw⟩]
    exact hcomp

/-- **The reduction, counting.** OpenAI's theorem for every width `≥ 2` gives exact counting. -/
theorem countingIsSubexponential_of (h : ∀ k, 2 ≤ k → OAIStatement k) :
    SubexponentialSharpSATCslib := by
  intro k
  have h2 := h (max k 2) (le_max_right _ _)
  unfold OAIStatement at h2
  obtain ⟨M, countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hM⟩ := h2
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = 8 * max k 2 + 7 := ⟨_, rfl⟩
  let D := 2 * d + 2 * e + 2
  refine ⟨D, fun r hr => ?_⟩
  obtain ⟨c₀, hc₀, hscale⟩ := scale_le A r hr
  let K : ℝ := C * κ ^ d * 2 ^ (c₀ + 1)
  let c : ℕ := ⌈K⌉₊ + 4 * κ + ⌈S * κ ^ e⌉₊ + 3 * κ * M.tapeCount
  refine ⟨c, ?_⟩
  unfold Turing.MultiTapeTM.ComputableInTimeAndSpace Turing.MultiTapeTM.ComputesFunInTimeAndSpace
  refine ⟨M.tapeCount, Sim.St M, inferInstance, Sim.tm M (some countTape), fun F => ?_⟩
  obtain ⟨n, G, hw⟩ := F
  have hw' : SAT.WidthAtMost (max k 2) (toOAI G) :=
    widthAtMost_toOAI fun C hC => (hw C hC).trans (le_max_left _ _)
  obtain ⟨time, final, htr, hcount, -, hstate, -, hlen, htime, hspace⟩ := hM n (toOAI G) hw'
  have hinput : encodeK k ⟨n, G, hw⟩ = Encoding.encodeCNF (toOAI G) := encode_eq G
  have hL : (encodeK k ⟨n, G, hw⟩).length = Encoding.formulaBitLength (toOAI G) := by
    rw [hinput]; rfl
  have htr' := htr
  rw [← hinput] at htr'
  obtain ⟨hcomp, hsp⟩ := Sim.simulate_count M htr' hstate hcount
  rw [hL] at hcomp hsp
  set L := Encoding.formulaBitLength (toOAI G) with hLdef
  set N := n + G.card + 1 with hN
  set w := countWord (SAT.count (toOAI G)) with hwdef
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength _
  have hwL : w.length ≤ L + 1 := by omega
  have hκ1 : 1 ≤ κ := by omega
  have hsize : L + 1 ≤ κ * N ^ 2 := by
    have := encoding_le_declaredSize_sq (toOAI G) hw'
    rw [card_toOAI, ← hLdef, ← hN, ← hκ] at this
    exact this
  have hsizeR : ((L : ℝ) + 1) ^ d ≤ (κ : ℝ) ^ d * (N : ℝ) ^ (2 * d) := by
    have := encoding_pow_le_declaredSize (toOAI G) hw' d
    rw [card_toOAI, ← hLdef, ← hN, ← hκ] at this
    exact this
  have hsizeR' : ((L : ℝ) + 1) ^ e ≤ (κ : ℝ) ^ e * (N : ℝ) ^ (2 * e) := by
    have := encoding_pow_le_declaredSize (toOAI G) hw' e
    rw [card_toOAI, ← hLdef, ← hN, ← hκ] at this
    exact this
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hκR : (1 : ℝ) ≤ κ := by exact_mod_cast hκ1
  have hpow : ∀ a ≤ D, (N : ℝ) ^ a ≤ (N : ℝ) ^ D := fun a ha => pow_le_pow_right₀ hN1R ha
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (n / r) := one_le_pow₀ (by norm_num)
  have hND : (0 : ℝ) ≤ (N : ℝ) ^ D := by positivity
  have hsizeℝ : ((L : ℝ) + 1) ≤ κ * (N : ℝ) ^ 2 := by exact_mod_cast hsize
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1R
  have h2D := hpow 2 (by omega)
  have hwLR : (w.length : ℝ) ≤ L + 1 := by exact_mod_cast hwL
  have hc : (c : ℝ) = ⌈K⌉₊ + 4 * κ + ⌈S * κ ^ e⌉₊ + 3 * κ * M.tapeCount := by simp [c]
  have hκ0 : (0 : ℝ) ≤ κ := by positivity
  have hκN : (1 : ℝ) ≤ κ * (N : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hκR hN2
  have hκND : (κ : ℝ) * (N : ℝ) ^ 2 ≤ κ * (N : ℝ) ^ D := mul_le_mul_of_nonneg_left h2D hκ0
  have hP : (κ : ℝ) * (N : ℝ) ^ D ≤ κ * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) :=
    le_mul_of_one_le_right (by positivity) hpow2
  have hout : binaryEmb (Fintype.card {a : Fin n → Bool // ∀ C ∈ G, ∃ l ∈ C, a l.1 = l.2}) = w := by
    rw [hwdef, count_toOAI]; rfl
  refine ⟨2 * L + 2 + time + (w.length + 1), ?_,
    (Sim.tm M (some countTape)).spaceUsed ((Sim.tm M (some countTape)).initCfg
      (encodeK k ⟨n, G, hw⟩)) (2 * L + 2 + time + (w.length + 1)), ?_, ?_⟩
  · -- time
    have hT : (time : ℝ) ≤ K * (N : ℝ) ^ (2 * d) * (2 : ℝ) ^ (n / r) := by
      have h2 : (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤
          2 ^ (c₀ + 1) * (2 : ℝ) ^ (n / r) := by
        calc (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n)
            ≤ (2 : ℝ) ^ ((n : ℝ) / r + c₀) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (hscale n)
          _ = 2 ^ c₀ * (2 : ℝ) ^ ((n : ℝ) / r) := by
              rw [Real.rpow_add (by norm_num)]; ring
          _ ≤ 2 ^ c₀ * (2 * (2 : ℝ) ^ (n / r)) :=
              mul_le_mul_of_nonneg_left (rpow_div_le n r hr) (by positivity)
          _ = 2 ^ (c₀ + 1) * (2 : ℝ) ^ (n / r) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
      calc (time : ℝ) ≤ C * ((L : ℝ) + 1) ^ d * 2 ^ (A * SqrtLog.Statement.runtimeScale n) :=
            htime
        _ ≤ C * ((κ : ℝ) ^ d * (N : ℝ) ^ (2 * d)) * (2 ^ (c₀ + 1) * (2 : ℝ) ^ (n / r)) := by
            gcongr
        _ = K * (N : ℝ) ^ (2 * d) * (2 : ℝ) ^ (n / r) := by ring
    have hK : K * (N : ℝ) ^ (2 * d) * (2 : ℝ) ^ (n / r) ≤
        (⌈K⌉₊ : ℝ) * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by
      have := hpow (2 * d) (by omega)
      have hKc := Nat.le_ceil K
      have hK0 : 0 ≤ K := by positivity
      gcongr
    have hLR : 3 * (L : ℝ) + 4 ≤ 4 * κ * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by
      linarith
    have hrest : (0 : ℝ) ≤ ((⌈S * κ ^ e⌉₊ : ℝ) + 3 * κ * M.tapeCount) *
        (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by positivity
    have hTot : ((2 * L + 2 + time + (w.length + 1) : ℕ) : ℝ) ≤
        (c : ℝ) * (N : ℝ) ^ D * (2 : ℝ) ^ (n / r) := by
      push_cast
      rw [hc]
      linarith
    show 2 * L + 2 + time + (w.length + 1) ≤ c * N ^ D * 2 ^ (n / r)
    exact_mod_cast hTot
  · -- space
    have hS' : (visitedSpace final : ℝ) ≤ S * ((L : ℝ) + 1) ^ e := hspace time final le_rfl htr
    have h1 : ((Sim.tm M (some countTape)).spaceUsed ((Sim.tm M (some countTape)).initCfg
        (encodeK k ⟨n, G, hw⟩)) (2 * L + 2 + time + (w.length + 1)) : ℝ) ≤
        visitedSpace final + M.tapeCount * ((L : ℝ) + w.length + 2) := by
      exact_mod_cast hsp
    have h2 : S * ((L : ℝ) + 1) ^ e ≤ ⌈S * κ ^ e⌉₊ * (N : ℝ) ^ D := by
      calc S * ((L : ℝ) + 1) ^ e ≤ S * ((κ : ℝ) ^ e * (N : ℝ) ^ (2 * e)) := by gcongr
        _ = (S * κ ^ e) * (N : ℝ) ^ (2 * e) := by ring
        _ ≤ ⌈S * κ ^ e⌉₊ * (N : ℝ) ^ D := by
            gcongr
            · exact Nat.le_ceil _
            · omega
    have h3 : (M.tapeCount : ℝ) * ((L : ℝ) + w.length + 2) ≤
        3 * κ * M.tapeCount * (N : ℝ) ^ D := by
      have hk : (0 : ℝ) ≤ M.tapeCount := Nat.cast_nonneg _
      have h2' : (L : ℝ) + w.length + 2 ≤ 3 * κ * (N : ℝ) ^ D := by linarith
      have := mul_le_mul_of_nonneg_left h2' hk
      linarith
    have hrest : (0 : ℝ) ≤ ((⌈K⌉₊ : ℝ) + 4 * κ) * (N : ℝ) ^ D := by positivity
    have hSp : ((Sim.tm M (some countTape)).spaceUsed ((Sim.tm M (some countTape)).initCfg
        (encodeK k ⟨n, G, hw⟩)) (2 * L + 2 + time + (w.length + 1)) : ℝ) ≤
        (c : ℝ) * (N : ℝ) ^ D := by
      rw [hc]; linarith
    show _ ≤ c * N ^ D
    exact_mod_cast hSp
  · -- correctness
    show (Sim.tm M (some countTape)).ComputesInTimeAndSpace (encodeK k ⟨n, G, hw⟩)
      (binaryEmb (Fintype.card {a : Fin n → Bool // ∀ C ∈ G, ∃ l ∈ C, a l.1 = l.2})) _ _
    rw [hout]
    exact hcomp

end ETHIsFalse.Proof
