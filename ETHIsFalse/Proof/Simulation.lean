import Mathlib
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.VisitedTape

/-!
# OpenAI's primitive machines run on CSLib's multi-tape Turing machines

`tm M` is a CSLib `MultiTapeTM` with one work tape per tape of OpenAI's `PrimitiveMachine M`.
It copies its read-only input onto the work tape of `M`'s input tape, rewinds it, and then makes
exactly one step for each step of `M`; when `M` halts with an answer, it outputs the answer and
halts. So it uses `2 · |input| + 2` steps more than `M` and the work cells `M` visits, plus at most
`|input| + 2` per tape. With `out = some c` it instead streams the word on `M`'s tape `c` to its
output tape when `M` halts.
-/

namespace ETHIsFalse.Proof.Sim

open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace Turing

variable (M : PrimitiveMachine) (out : Option (Fin M.tapeCount))

/-- Control states: copy the input, rewind the copy, run `M` in state `q`, emit the result. -/
inductive St (M : PrimitiveMachine) where
  | copy
  | rewind
  | run (q : Fin M.stateCount)
  | emit

instance : Finite (St M) :=
  Finite.of_injective
    (fun s : St M => match s with
      | .copy => (none : Option (Option (Option (Fin M.stateCount))))
      | .rewind => some none
      | .emit => some (some none)
      | .run q => some (some (some q)))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Do `a` on work tape `j` and nothing on the others. -/
def only (j : Fin M.tapeCount) (a : Option (Option Bool) × SignType) :
    Fin M.tapeCount → Option (Option Bool) × SignType :=
  fun i => if i = j then a else (none, 0)

/-- A primitive tape statement as a CSLib work-tape action. -/
def stmtAction : TM0.Stmt (Option Bool) → Option (Option Bool) × SignType
  | .move .left => (none, -1)
  | .move .right => (none, 1)
  | .write s => (some s, 0)

/-- The transition function. When `M` halts with `answer`, output `answer` and halt
(`out = none`), or stream tape `c` to the output (`out = some c`). -/
def tr : St M → Option Bool → (Fin M.tapeCount → Option Bool) → Action M.tapeCount Bool (St M)
  | .copy, some b, _ => ⟨1, only M M.inputTape (some (some b), 1), none, some .copy⟩
  | .copy, none, _ => ⟨0, only M M.inputTape (none, -1), none, some .rewind⟩
  | .rewind, _, w =>
    match w M.inputTape with
    | some _ => ⟨0, only M M.inputTape (none, -1), none, some .rewind⟩
    | none => ⟨0, only M M.inputTape (none, 1), none, some (.run M.start)⟩
  | .run q, _, w =>
    match M.transition q (w (M.scan q)) with
    | .inl answer =>
      match out with
      | none => ⟨0, fun _ => (none, 0), some answer, none⟩
      | some _ => ⟨0, fun _ => (none, 0), none, some .emit⟩
    | .inr (q', a) => ⟨0, only M (M.scan q) (stmtAction a), none, some (.run q')⟩
  | .emit, _, w =>
    match out with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some c =>
      match w c with
      | some b => ⟨0, only M c (none, 1), some b, some .emit⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩

/-- The simulating machine. -/
def tm : MultiTapeTM M.tapeCount Bool (St M) := ⟨.copy, tr M out⟩

variable {out}

/-! ## Tapes -/

/-- The work tape `f` with its head at `p` holds the Mathlib tape `T`. -/
def Represents (T : Tape (Option Bool)) (f : ℤ → Option Bool) (p : ℤ) : Prop :=
  ∀ i, f (p + i) = T.nth i

theorem represents_write {T : Tape (Option Bool)} {f : ℤ → Option Bool} {p : ℤ}
    (h : Represents T f p) (s : Option Bool) :
    Represents (T.write s) (Function.update f p s) p := by
  intro i
  rw [Tape.write_nth]
  by_cases hi : i = 0
  · subst hi; simp
  · rw [Function.update_of_ne (by omega), h i, if_neg hi]

theorem represents_left {T : Tape (Option Bool)} {f : ℤ → Option Bool} {p : ℤ}
    (h : Represents T f p) : Represents (T.move Dir.left) f (p + -1) := by
  intro i
  rw [Tape.move_left_nth, ← h]
  congr 1; ring

theorem represents_right {T : Tape (Option Bool)} {f : ℤ → Option Bool} {p : ℤ}
    (h : Represents T f p) : Represents (T.move Dir.right) f (p + 1) := by
  intro i
  rw [Tape.move_right_nth, ← h]
  congr 1; ring

/-- The cells of a word written from position `0`. -/
def wordTape (w : List Bool) : ℤ → Option Bool := fun z => if z < 0 then none else w[z.toNat]?

theorem getI_map_some (w : List Bool) (n : ℕ) : (w.map some).getI n = w[n]? := by
  by_cases h : n < w.length
  · rw [List.getI_eq_getElem _ (by simpa using h)]
    simp [List.getElem?_eq_getElem h]
  · rw [List.getI_eq_default _ (by simpa using h), List.getElem?_eq_none (by omega)]
    rfl

theorem nth_mk₁_map (w : List Bool) (i : ℤ) :
    (Tape.mk₁ (w.map some)).nth i = wordTape w i := by
  rcases i with n | n
  · have : (Tape.mk₁ (w.map some)).nth (n : ℤ) = w[n]? := by
      simp [Tape.mk₁, Tape.mk₂, getI_map_some]
    show (Tape.mk₁ (w.map some)).nth (n : ℤ) = wordTape w (n : ℤ)
    rw [this, wordTape, if_neg (by omega), Int.toNat_natCast]
  · have h : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    simp only [wordTape, h, if_true]
    rfl

theorem represents_init (w : List Bool) : Represents (Tape.mk₁ (w.map some)) (wordTape w) 0 := by
  intro i; rw [zero_add, nth_mk₁_map]

theorem represents_blank : Represents (Tape.mk₁ []) (fun _ => none) 0 := by
  intro i; simpa [wordTape] using (nth_mk₁_map [] i).symm

/-! ## One step of `M` is one step of `tm M` -/

theorem step_some {input : List Bool} {cfg : Cfg M.tapeCount Bool (St M) input} {q : St M}
    (h : cfg.state = some q) :
    (tm M out).step cfg = (tr M out q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  unfold MultiTapeTM.step
  rw [h]
  rfl

variable (out) in
/-- `d` simulates the located configuration `c` of `M`. -/
structure Rel {input : List Bool} (c : LocatedCfg M) (d : Cfg M.tapeCount Bool (St M) input) :
    Prop where
  state : d.state = Sum.elim (fun _ => out.map fun _ => .emit) (fun q => some (.run q)) c.config.state
  output : d.output = Sum.elim (fun a => out.elim [a] fun _ => []) (fun _ => []) c.config.state
  pos : ∀ j, d.workTapePos j = c.position j
  tape : ∀ j, Represents (c.config.tapes j) (d.workTapes j) (d.workTapePos j)

theorem stmtAction_snd (a : TM0.Stmt (Option Bool)) :
    ((stmtAction a).2 : ℤ) = headDisplacement a := by
  rcases a with (_ | _) | _ <;> simp [stmtAction, headDisplacement]

theorem represents_stmt {T : Tape (Option Bool)} {f : ℤ → Option Bool} {p : ℤ}
    (h : Represents T f p) (a : TM0.Stmt (Option Bool)) :
    Represents
      (match a with
        | .move direction => T.move direction
        | .write symbol => T.write symbol)
      (match (stmtAction a).1 with
        | none => f
        | some s => Function.update f p s)
      (p + (stmtAction a).2) := by
  rcases a with (_ | _) | s
  · simpa [stmtAction] using represents_left h
  · simpa [stmtAction] using represents_right h
  · simpa [stmtAction] using represents_write h s

theorem rel_step {input : List Bool} {c c' : LocatedCfg M} {d : Cfg M.tapeCount Bool (St M) input}
    (h : Rel M out c d) (hs : locatedStep M c = some c') : Rel M out c' ((tm M out).step d) := by
  have hcfg := locatedStep_config hs
  rcases hq : c.config.state with a | q
  · simp [PrimitiveMachine.step, hq] at hcfg
  have hd : d.state = some (.run q) := by simp [h.state, hq]
  have hout : d.output = [] := by simp [h.output, hq]
  have hhead : d.workTapeSymbols (M.scan q) = (c.config.tapes (M.scan q)).head := by
    have := h.tape (M.scan q) 0
    simpa [Cfg.workTapeSymbols] using this
  have hstep := step_some M (out := out) hd
  rcases ht : M.transition q (c.config.tapes (M.scan q)).head with a | ⟨q', act⟩
  · have hc' : c'.config = ⟨.inl a, c.config.tapes⟩ := by
      simp [PrimitiveMachine.step, hq, ht] at hcfg; exact hcfg.symm
    have hpos := locatedStep_position_halt hs hq ht
    rw [hstep]
    rcases out with _ | ct
    · have htr : tr M none (.run q) d.inputSymbol d.workTapeSymbols =
          ⟨0, fun _ => (none, 0), some a, none⟩ := by
        simp only [tr, hhead, ht]
      rw [htr]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hc']
      · simp [hc', hout]
      · intro j; simp [h.pos j, hpos]
      · intro j; simpa [hc'] using h.tape j
    · have htr : tr M (some ct) (.run q) d.inputSymbol d.workTapeSymbols =
          ⟨0, fun _ => (none, 0), none, some .emit⟩ := by
        simp only [tr, hhead, ht]
      rw [htr]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hc']
      · simp [hc', hout]
      · intro j; simp [h.pos j, hpos]
      · intro j; simpa [hc'] using h.tape j
  · have hpos := locatedStep_position_action hs hq ht
    have htr : tr M out (.run q) d.inputSymbol d.workTapeSymbols =
        ⟨0, only M (M.scan q) (stmtAction act), none, some (.run q')⟩ := by
      simp only [tr, hhead, ht]
    rw [hstep, htr]
    rcases act with (_ | _) | s <;>
    · simp only [PrimitiveMachine.step, hq, ht, Option.some.injEq] at hcfg
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [← hcfg]
      · simp [← hcfg, hout]
      · intro j
        by_cases hj : j = M.scan q
        · subst hj; simp [only, hpos, h.pos, stmtAction_snd]
        · simp [only, hj, hpos, h.pos j]
      · intro j
        by_cases hj : j = M.scan q
        · subst hj
          first
            | simpa [only, ← hcfg, stmtAction] using represents_left (h.tape (M.scan q))
            | simpa [only, ← hcfg, stmtAction] using represents_right (h.tape (M.scan q))
            | simpa [only, ← hcfg, stmtAction] using represents_write (h.tape (M.scan q)) s
        · simpa [only, hj, ← hcfg, Function.update_of_ne hj] using h.tape j

/-- Along a trace of `M`, every prefix is simulated by the same number of steps of `tm M`. -/
theorem rel_runFrom {input : List Bool} {t : ℕ} {c cf : LocatedCfg M}
    (htr : Trace (locatedStep M) t c cf) :
    ∀ {d : Cfg M.tapeCount Bool (St M) input}, Rel M out c d →
      ∀ s ≤ t, ∃ cs, Trace (locatedStep M) s c cs ∧ Rel M out cs ((tm M out).runFrom d s) := by
  induction htr with
  | refl a =>
    intro d h s hs
    obtain rfl : s = 0 := by omega
    exact ⟨a, .refl a, by simpa using h⟩
  | @cons n a b c' hab _ ih =>
    intro d h s hs
    rcases s with _ | s
    · exact ⟨a, .refl a, by simpa using h⟩
    · obtain ⟨cs, hcs, hrel⟩ := ih (rel_step M h hab) s (by omega)
      exact ⟨cs, .cons hab hcs, by rwa [MultiTapeTM.runFrom_succ_eq_step]⟩

/-! ## Copying and rewinding the input -/

section Copy

variable {input : List Bool}

/-- After copying `j` input symbols. -/
def copyCfg (input : List Bool) (j : ℕ) (hj : j ≤ input.length) :
    Cfg M.tapeCount Bool (St M) input :=
  ⟨some .copy, ⟨j + 1, by omega⟩,
    fun t => if t = M.inputTape then wordTape (input.take j) else fun _ => none,
    fun t => if t = M.inputTape then (j : ℤ) else 0, []⟩

/-- After `i + 1` steps back over the copy. -/
def rewindCfg (input : List Bool) (i : ℕ) :
    Cfg M.tapeCount Bool (St M) input :=
  ⟨some .rewind, ⟨input.length + 1, by omega⟩,
    fun t => if t = M.inputTape then wordTape input else fun _ => none,
    fun t => if t = M.inputTape then (input.length : ℤ) - 1 - i else 0, []⟩

/-- Ready to run `M` on the copied input. -/
def startCfg (input : List Bool) : Cfg M.tapeCount Bool (St M) input :=
  ⟨some (.run M.start), ⟨input.length + 1, by omega⟩,
    fun t => if t = M.inputTape then wordTape input else fun _ => none, fun _ => 0, []⟩

theorem init_eq : (tm M out).initCfg input = copyCfg M input 0 (Nat.zero_le _) := by
  refine Cfg.ext rfl ?_ (funext fun t => funext fun z => ?_) (funext fun t => ?_) rfl
  · apply Fin.ext; simp [copyCfg, tm]
  · by_cases ht : t = M.inputTape <;> simp [copyCfg, tm, ht, wordTape]
  · by_cases ht : t = M.inputTape <;> simp [copyCfg, tm, ht]

theorem wordTape_neg (w : List Bool) {z : ℤ} (hz : z < 0) : wordTape w z = none := by
  simp [wordTape, hz]

theorem wordTape_ne_none (w : List Bool) {z : ℤ} (h0 : 0 ≤ z) (h1 : z < w.length) :
    wordTape w z ≠ none := by
  rw [wordTape, if_neg (not_lt.mpr h0)]
  exact List.getElem?_eq_none_iff.not.mpr (by omega)

theorem wordTape_take_succ (j : ℕ) (hj : j < input.length) :
    Function.update (wordTape (input.take j)) (j : ℤ) (some input[j]) =
      wordTape (input.take (j + 1)) := by
  funext z
  rcases lt_or_ge z 0 with h0 | h0
  · rw [Function.update_of_ne (by omega), wordTape_neg _ h0, wordTape_neg _ h0]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  by_cases hm : m = j
  · subst hm
    rw [Function.update_self]
    simp [wordTape, List.getElem?_take, hj]
  · rw [Function.update_of_ne (by exact_mod_cast hm)]
    simp only [wordTape, Int.toNat_natCast, List.getElem?_take]
    split_ifs <;> first | rfl | omega

theorem step_copy (j : ℕ) (hj : j < input.length) :
    (tm M out).step (copyCfg M input j hj.le) = copyCfg M input (j + 1) hj := by
  have hsym : (copyCfg M input j hj.le).inputSymbol = some input[j] :=
    inputSymbolInner j (by show j + 1 = 1 + j; omega) hj
  rw [step_some M (q := .copy) rfl, hsym]
  simp only [tr]
  refine Cfg.ext rfl ?_ (funext fun t => funext fun z => ?_) (funext fun t => ?_) ?_
  · simp only [Action.apply]
    rw [show (1 : SignType) = .pos from rfl,
      moveInputPos_pos_of_ne_right _ (by show j + 1 ≠ input.length + 1; omega)]
    rfl
  · by_cases ht : t = M.inputTape
    · subst ht; simp [copyCfg, only, ← wordTape_take_succ j hj]
    · simp [copyCfg, only, ht]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [copyCfg, only]
    · simp [copyCfg, only, ht]
  · simp [copyCfg]

theorem inputSymbol_end {cfg : Cfg M.tapeCount Bool (St M) input}
    (h : cfg.inputPos.val = input.length + 1) : cfg.inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

theorem step_copy_end :
    (tm M out).step (copyCfg M input input.length le_rfl) = rewindCfg M input 0 := by
  have hsym : (copyCfg M input input.length le_rfl).inputSymbol = none :=
    inputSymbol_end M rfl
  rw [step_some M (q := .copy) rfl, hsym]
  simp only [tr]
  refine Cfg.ext rfl ?_ (funext fun t => funext fun z => ?_) (funext fun t => ?_) ?_
  · simp [Action.apply, copyCfg, rewindCfg]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [copyCfg, rewindCfg, only]
    · simp [copyCfg, rewindCfg, only, ht]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [copyCfg, rewindCfg, only]; omega
    · simp [copyCfg, rewindCfg, only, ht]
  · simp [copyCfg, rewindCfg]

theorem step_rewind (i : ℕ) (hi : i < input.length) :
    (tm M out).step (rewindCfg M input i) = rewindCfg M input (i + 1) := by
  have hsym : (rewindCfg M input i).workTapeSymbols M.inputTape ≠ none := by
    simp only [Cfg.workTapeSymbols, rewindCfg, if_pos]
    exact wordTape_ne_none input (by omega) (by omega)
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hsym
  rw [step_some M (q := .rewind) rfl]
  simp only [tr, hb]
  refine Cfg.ext rfl ?_ (funext fun t => funext fun z => ?_) (funext fun t => ?_) ?_
  · simp [Action.apply, rewindCfg]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [rewindCfg, only]
    · simp [rewindCfg, only, ht]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [rewindCfg, only]; ring
    · simp [rewindCfg, only, ht]
  · simp [rewindCfg]

theorem step_rewind_end :
    (tm M out).step (rewindCfg M input input.length) = startCfg M input := by
  have hsym : (rewindCfg M input input.length).workTapeSymbols M.inputTape = none := by
    simp only [Cfg.workTapeSymbols, rewindCfg, if_pos]
    exact wordTape_neg input (by omega)
  rw [step_some M (q := .rewind) rfl]
  simp only [tr, hsym]
  refine Cfg.ext rfl ?_ (funext fun t => funext fun z => ?_) (funext fun t => ?_) ?_
  · simp [Action.apply, rewindCfg, startCfg]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [rewindCfg, startCfg, only]
    · simp [rewindCfg, startCfg, only, ht]
  · by_cases ht : t = M.inputTape
    · subst ht; simp [rewindCfg, startCfg, only]
    · simp [rewindCfg, startCfg, only, ht]
  · simp [rewindCfg, startCfg]

theorem runFrom_copy (j : ℕ) (hj : j ≤ input.length) :
    (tm M out).runFrom ((tm M out).initCfg input) j = copyCfg M input j hj := by
  induction j with
  | zero => rw [MultiTapeTM.runFrom_zero, init_eq]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), step_copy M j (by omega)]

theorem runFrom_rewind (i : ℕ) (hi : i ≤ input.length) :
    (tm M out).runFrom ((tm M out).initCfg input) (input.length + 1 + i) = rewindCfg M input i := by
  induction i with
  | zero =>
    rw [Nat.add_zero, MultiTapeTM.runFrom_succ_eq_step', runFrom_copy M _ le_rfl,
      step_copy_end]
  | succ i ih =>
    rw [← Nat.add_assoc, MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      step_rewind M i (by omega)]

theorem runFrom_start :
    (tm M out).runFrom ((tm M out).initCfg input) (2 * input.length + 2) = startCfg M input := by
  rw [show 2 * input.length + 2 = input.length + 1 + input.length + 1 by ring,
    MultiTapeTM.runFrom_succ_eq_step', runFrom_rewind M _ le_rfl, step_rewind_end]

theorem rel_start : Rel M out (locatedInit M input) (startCfg M input) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [startCfg, locatedInit, PrimitiveMachine.init]
  · simp [startCfg, locatedInit, PrimitiveMachine.init]
  · intro j; simp [startCfg, locatedInit]
  · intro j
    by_cases hj : j = M.inputTape
    · subst hj; simpa [startCfg, locatedInit, PrimitiveMachine.init] using represents_init input
    · simpa [startCfg, locatedInit, PrimitiveMachine.init, hj] using represents_blank

/-- During copying and rewinding, every head stays within `[-1, |input|]`. -/
theorem copy_pos (s : ℕ) (hs : s ≤ 2 * input.length + 2) (j : Fin M.tapeCount) :
    -1 ≤ ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j ∧
      ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j ≤ input.length := by
  by_cases h1 : s ≤ input.length
  · rw [runFrom_copy M s h1]
    by_cases hj : j = M.inputTape <;> simp [copyCfg, hj] <;> omega
  by_cases h2 : s ≤ 2 * input.length + 1
  · obtain ⟨i, rfl⟩ : ∃ i, s = input.length + 1 + i := ⟨s - (input.length + 1), by omega⟩
    rw [runFrom_rewind M i (by omega)]
    by_cases hj : j = M.inputTape <;> simp [rewindCfg, hj] <;> omega
  · obtain rfl : s = 2 * input.length + 2 := by omega
    rw [runFrom_start]
    simp [startCfg]

end Copy

/-! ## The simulation theorem -/

theorem card_image_le_of_bounds {S : Finset ℕ} (f : ℕ → ℤ) (lo hi : ℤ)
    (h : ∀ s ∈ S, lo ≤ f s ∧ f s ≤ hi) : (S.image f).card ≤ (hi + 1 - lo).toNat := by
  calc (S.image f).card ≤ (Finset.Icc lo hi).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_Icc.mpr (h s hs)
    _ = (hi + 1 - lo).toNat := Int.card_Icc lo hi

/-- The run of `tm M out` up to the halting of `M`: it reaches the configuration simulating
`final` after `2 · |input| + 2 + t` steps, its heads staying in `final`'s envelope widened by
`[-1, |input|]`. -/
theorem sim_core {input : List Bool} {t : ℕ} {final : LocatedCfg M}
    (htr : Trace (locatedStep M) t (locatedInit M input) final) :
    (tm M out).runFrom ((tm M out).initCfg input) (2 * input.length + 2 + t) =
      (tm M out).runFrom (startCfg M input) t ∧
    Rel M out final ((tm M out).runFrom (startCfg M input) t) ∧
    (∀ j, final.lower j ≤ 0 ∧ 0 ≤ final.upper j) ∧
    ∀ j, ∀ s ≤ 2 * input.length + 2 + t,
      final.lower j - 1 ≤ ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j ∧
        ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j ≤
          final.upper j + input.length := by
  have hrun := rel_runFrom M htr (rel_start M (out := out) (input := input))
  have hfinal : Rel M out final ((tm M out).runFrom (startCfg M input) t) := by
    obtain ⟨cs, hcs, hrel⟩ := hrun t le_rfl
    rwa [trace_same_length_unique hcs htr] at hrel
  have hlow : ∀ j, final.lower j ≤ 0 ∧ 0 ≤ final.upper j := by
    intro j
    have := locatedTrace_expands htr j
    simp only [locatedInit, Int.ofNat_eq_coe] at this
    split_ifs at this <;> omega
  refine ⟨by rw [MultiTapeTM.runFrom_add, runFrom_start], hfinal, hlow, ?_⟩
  intro j s hs
  have := hlow j
  by_cases hc : s ≤ 2 * input.length + 2
  · have := copy_pos M (out := out) s hc j
    omega
  · obtain ⟨s', rfl⟩ : ∃ s', s = 2 * input.length + 2 + s' :=
      ⟨s - (2 * input.length + 2), by omega⟩
    rw [MultiTapeTM.runFrom_add, runFrom_start]
    obtain ⟨cs, hcs, hrel⟩ := hrun s' (by omega)
    have henc := locatedTrace_init_encloses hcs j
    have hexp := locatedTrace_expands (trace_suffix htr hcs (by omega)) j
    rw [hrel.pos j]
    omega

/-- Heads within `final`'s envelope widened by `[-1, B]` touch at most `B + 2` extra cells a tape. -/
theorem space_le {input : List Bool} {T B : ℕ} {final : LocatedCfg M}
    (hlow : ∀ j, final.lower j ≤ 0 ∧ 0 ≤ final.upper j)
    (hb : ∀ j, ∀ s ≤ T,
      final.lower j - 1 ≤ ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j ∧
        ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j ≤ final.upper j + B) :
    (tm M out).spaceUsed ((tm M out).initCfg input) T ≤
      visitedSpace final + M.tapeCount * (B + 2) := by
  unfold MultiTapeTM.spaceUsed MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
  unfold visitedSpace
  calc ∑ j, ((Finset.range (T + 1)).image fun s =>
          ((tm M out).runFrom ((tm M out).initCfg input) s).workTapePos j).card
      ≤ ∑ j : Fin M.tapeCount, ((final.upper j - final.lower j + 1).toNat + (B + 2)) := by
        apply Finset.sum_le_sum
        intro j _
        refine (card_image_le_of_bounds _ _ _
          (fun s hs => hb j s (by have := Finset.mem_range.mp hs; omega))).trans ?_
        have := hlow j
        omega
    _ = _ := by
        rw [Finset.sum_add_distrib]
        simp

/-- **Simulation, decision.** If `M` halts on `input` with answer `answer` after `t` steps, then
`tm M none` outputs `[answer]` after `2 · |input| + 2 + t` steps, using at most the cells `M`
visited plus `|input| + 2` per tape. -/
theorem simulate {input : List Bool} {t : ℕ} {final : LocatedCfg M} {answer : Bool}
    (htr : Trace (locatedStep M) t (locatedInit M input) final)
    (hans : final.config.state = .inl answer) :
    (tm M none).ComputesInTimeAndSpace input [answer] (2 * input.length + 2 + t)
      ((tm M none).spaceUsed ((tm M none).initCfg input) (2 * input.length + 2 + t)) ∧
    (tm M none).spaceUsed ((tm M none).initCfg input) (2 * input.length + 2 + t) ≤
      visitedSpace final + M.tapeCount * (input.length + 2) := by
  obtain ⟨hT, hfinal, hlow, hb⟩ := sim_core M (out := none) htr
  refine ⟨?_, space_le M hlow hb⟩
  unfold MultiTapeTM.ComputesInTimeAndSpace
  refine ⟨?_, ?_, rfl⟩
  · rw [hT, hfinal.state, hans]; rfl
  · rw [hT, hfinal.output, hans]; rfl

/-! ## Emitting a word -/

theorem emit_run {input : List Bool} {c : Fin M.tapeCount} {w : List Bool}
    {d : Cfg M.tapeCount Bool (St M) input} (hs : d.state = some .emit) (ho : d.output = [])
    (hrep : Represents (Tape.mk₁ (w.map some)) (d.workTapes c) (d.workTapePos c)) :
    ∀ i ≤ w.length, (tm M (some c)).runFrom d i =
      ⟨some .emit, d.inputPos, d.workTapes,
        Function.update d.workTapePos c (d.workTapePos c + i), w.take i⟩ := by
  intro i hi
  induction i with
  | zero =>
    rw [MultiTapeTM.runFrom_zero]
    refine Cfg.ext hs rfl rfl (funext fun j => ?_) (by simp [ho])
    by_cases hj : j = c
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  | succ i ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), step_some M (q := .emit) rfl]
    have hsym : (⟨some .emit, d.inputPos, d.workTapes,
        Function.update d.workTapePos c (d.workTapePos c + i), w.take i⟩ :
          Cfg M.tapeCount Bool (St M) input).workTapeSymbols c = some w[i] := by
      simp only [Cfg.workTapeSymbols, Function.update_self]
      rw [hrep i, nth_mk₁_map, wordTape, if_neg (by omega), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    simp only [tr, hsym]
    refine Cfg.ext rfl (by simp) (funext fun j => by by_cases hj : j = c <;> simp [only, hj])
      (funext fun j => ?_) ?_
    · by_cases hj : j = c
      · subst hj; simp [only, add_assoc]
      · simp [only, hj, Function.update_of_ne hj]
    · show List.take i w ++ (some w[i]).toList = List.take (i + 1) w
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

theorem emit_halt {input : List Bool} {c : Fin M.tapeCount} {w : List Bool}
    {d : Cfg M.tapeCount Bool (St M) input} (hs : d.state = some .emit) (ho : d.output = [])
    (hrep : Represents (Tape.mk₁ (w.map some)) (d.workTapes c) (d.workTapePos c)) :
    ((tm M (some c)).runFrom d (w.length + 1)).state = none ∧
      ((tm M (some c)).runFrom d (w.length + 1)).output = w ∧
      ∀ i ≤ w.length + 1, ∀ j, ((tm M (some c)).runFrom d i).workTapePos j =
        d.workTapePos j + if j = c then (min i w.length : ℕ) else 0 := by
  have hlast := emit_run M hs ho hrep w.length le_rfl
  have hsym : (⟨some .emit, d.inputPos, d.workTapes,
      Function.update d.workTapePos c (d.workTapePos c + w.length), w.take w.length⟩ :
        Cfg M.tapeCount Bool (St M) input).workTapeSymbols c = none := by
    simp only [Cfg.workTapeSymbols, Function.update_self]
    rw [hrep w.length, nth_mk₁_map, wordTape, if_neg (by omega), Int.toNat_natCast]
    exact List.getElem?_eq_none (by omega)
  have hstep : (tm M (some c)).runFrom d (w.length + 1) =
      ⟨none, d.inputPos, d.workTapes,
        Function.update d.workTapePos c (d.workTapePos c + w.length), w⟩ := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hlast, step_some M (q := .emit) rfl]
    simp only [tr, hsym]
    refine Cfg.ext rfl (by simp) rfl (funext fun j => by simp) ?_
    simp
  refine ⟨by rw [hstep], by rw [hstep], fun i hi j => ?_⟩
  rcases Nat.lt_or_ge i (w.length + 1) with h | h
  · rw [emit_run M hs ho hrep i (by omega)]
    by_cases hj : j = c
    · subst hj; simp [show min i w.length = i by omega]
    · simp [hj, Function.update_of_ne hj]
  · obtain rfl : i = w.length + 1 := by omega
    rw [hstep]
    by_cases hj : j = c
    · subst hj; simp
    · simp [hj, Function.update_of_ne hj]

/-- **Simulation, counting.** If `M` halts on `input` after `t` steps with the word `w` on tape
`c`, then `tm M (some c)` outputs `w` after `2 · |input| + 2 + t + |w| + 1` steps, using at most
the cells `M` visited plus `|input| + |w| + 2` per tape. -/
theorem simulate_count {input : List Bool} {t : ℕ} {final : LocatedCfg M} {answer : Bool}
    {c : Fin M.tapeCount} {w : List Bool}
    (htr : Trace (locatedStep M) t (locatedInit M input) final)
    (hans : final.config.state = .inl answer)
    (hw : final.config.tapes c = Tape.mk₁ (w.map some)) :
    (tm M (some c)).ComputesInTimeAndSpace input w (2 * input.length + 2 + t + (w.length + 1))
      ((tm M (some c)).spaceUsed ((tm M (some c)).initCfg input)
        (2 * input.length + 2 + t + (w.length + 1))) ∧
    (tm M (some c)).spaceUsed ((tm M (some c)).initCfg input)
        (2 * input.length + 2 + t + (w.length + 1)) ≤
      visitedSpace final + M.tapeCount * (input.length + w.length + 2) := by
  obtain ⟨hT, hfinal, hlow, hb⟩ := sim_core M (out := some c) htr
  set d := (tm M (some c)).runFrom (startCfg M input) t
  have hs : d.state = some .emit := by rw [hfinal.state, hans]; rfl
  have ho : d.output = [] := by rw [hfinal.output, hans]; rfl
  have hrep : Represents (Tape.mk₁ (w.map some)) (d.workTapes c) (d.workTapePos c) := by
    rw [← hw]; exact hfinal.tape c
  obtain ⟨hhalt, hout, hpos⟩ := emit_halt M hs ho hrep
  have hTot : ∀ i, (tm M (some c)).runFrom ((tm M (some c)).initCfg input)
      (2 * input.length + 2 + t + i) = (tm M (some c)).runFrom d i := by
    intro i; rw [MultiTapeTM.runFrom_add, hT]
  refine ⟨?_, space_le M hlow fun j s hs' => ?_⟩
  · unfold MultiTapeTM.ComputesInTimeAndSpace
    exact ⟨by rw [hTot]; exact hhalt, by rw [hTot]; exact hout, rfl⟩
  · by_cases hc : s ≤ 2 * input.length + 2 + t
    · have := hb j s hc
      omega
    · obtain ⟨i, rfl⟩ : ∃ i, s = 2 * input.length + 2 + t + i :=
        ⟨s - (2 * input.length + 2 + t), by omega⟩
      rw [hTot, hpos i (by omega) j, hfinal.pos j]
      have hd := hb j (2 * input.length + 2 + t) le_rfl
      rw [hT, hfinal.pos j] at hd
      have := hlow j
      split_ifs <;> omega

end ETHIsFalse.Proof.Sim
