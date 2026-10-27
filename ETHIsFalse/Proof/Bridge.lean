import ETHIsFalse.Statement
import OAI.Algorithms.SubexponentialSAT.Encoding

/-!
# From Mathlib formulas to the OpenAI formula syntax

`toOAI` renames the literal `(v, b)` to OpenAI's `⟨v, b⟩`. The readable `encodeSet` is OpenAI's
`encodeCNF` after this renaming, so it is injective and its length obeys OpenAI's bounds.
-/

namespace ETHIsFalse.Proof

open OAI.Algorithms.SubexponentialSAT

/-- Formulas with `n` variables as sets of sets of literals, as `ETHIsFalse.clauseSet` gives. -/
abbrev CNF (n : ℕ) := Finset (Finset (Fin n × Bool))

/-- `ETHIsFalse.encode` on sets of clauses: `encode n F = encodeSet n (clauseSet F)`. -/
def encodeSet (n : ℕ) (F : CNF n) : List Bool :=
  unary n ++ listCode (listCode unary) ((F.image clauseNumbers).sort (· ≤ ·))

theorem encode_eq_encodeSet {n : ℕ} (F : Std.Sat.CNF (Fin n)) :
    encode n F = encodeSet n (clauseSet F) := rfl

/-- The literal `(v, b)` as an OpenAI literal. -/
def toLit {n : ℕ} (l : Fin n × Bool) : SAT.Literal (Fin n) := ⟨l.1, l.2⟩

theorem toLit_injective {n : ℕ} : Function.Injective (toLit (n := n)) := by
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  simp only [toLit, SAT.Literal.mk.injEq] at h
  rw [h.1, h.2]

/-- A formula as an OpenAI formula. -/
def toOAI {n : ℕ} (F : CNF n) : SAT.CNF (Fin n) := F.image fun C => C.image toLit

theorem toOAI_injective {n : ℕ} : Function.Injective (toOAI (n := n)) :=
  Finset.image_injective (Finset.image_injective toLit_injective)

theorem card_toOAI {n : ℕ} (F : CNF n) : (toOAI F).card = F.card :=
  Finset.card_image_of_injective _ (Finset.image_injective toLit_injective)

theorem widthAtMost_toOAI {n k : ℕ} {F : CNF n} (h : ∀ C ∈ F, C.card ≤ k) :
    SAT.WidthAtMost k (toOAI F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
  rw [Finset.card_image_of_injective _ toLit_injective]
  exact h D hD

theorem eval_toOAI {n : ℕ} (F : CNF n) (a : Fin n → Bool) :
    SAT.CNF.eval a (toOAI F) = true ↔ ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2 := by
  simp only [SAT.CNF.eval_eq_true, toOAI, Finset.forall_mem_image, SAT.Clause.eval_eq_true,
    Finset.exists_mem_image, SAT.Literal.eval_eq_true, toLit]

theorem satisfiable_toOAI {n : ℕ} (F : CNF n) :
    SAT.Satisfiable (toOAI F) ↔ ∃ a : Fin n → Bool, ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2 := by
  unfold SAT.Satisfiable
  exact exists_congr fun a => eval_toOAI F a

theorem count_toOAI {n : ℕ} (F : CNF n) :
    SAT.count (toOAI F) = Fintype.card {a : Fin n → Bool // ∀ C ∈ F, ∃ l ∈ C, a l.1 = l.2} := by
  rw [Fintype.card_subtype]
  unfold SAT.count SAT.satisfyingAssignments
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eval_toOAI F a

theorem frame_eq (w : List Bool) : frame w = Encoding.frame w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, Encoding.frame_cons, ← ih]

theorem listCode_eq {α : Type*} (code : α → List Bool) (as : List α) :
    listCode code as = Encoding.encodeList code as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [listCode, Encoding.encodeList, frame_eq, ← ih]

theorem clauseNumbers_eq {n : ℕ} (C : Finset (Fin n × Bool)) :
    clauseNumbers C = Encoding.clauseNumbers (C.image toLit) := by
  unfold clauseNumbers Encoding.clauseNumbers
  rw [Finset.image_image]
  congr 2
  funext l
  obtain ⟨v, b⟩ := l
  cases b <;> simp [Encoding.literalCode, toLit, Bool.toNat]

/-- The readable encoding is OpenAI's `encodeCNF`. -/
theorem encode_eq {n : ℕ} (F : CNF n) : encodeSet n F = Encoding.encodeCNF (toOAI F) := by
  have hl : listCode unary = Encoding.encodeList Encoding.encodeNat :=
    funext (listCode_eq unary)
  have hc : (clauseNumbers : Finset (Fin n × Bool) → List ℕ) =
      Encoding.clauseNumbers ∘ fun C => C.image toLit :=
    funext clauseNumbers_eq
  simp only [encodeSet, Encoding.encodeCNF, Encoding.encodeCNFBody, Encoding.cnfNumbers, toOAI,
    Finset.image_image, listCode_eq, hl, hc]
  rfl

theorem encode_injective : Function.Injective fun F : Σ n, CNF n => encodeSet F.1 F.2 := by
  rintro ⟨n, F⟩ ⟨m, G⟩ h
  dsimp only at h
  rw [encode_eq, encode_eq] at h
  have h' : Encoding.encodeFormula ⟨n, toOAI F⟩ = Encoding.encodeFormula ⟨m, toOAI G⟩ := h
  have := Encoding.encodeFormula_injective h'
  obtain ⟨rfl, hFG⟩ := Sigma.mk.inj_iff.mp this
  rw [toOAI_injective (eq_of_heq hFG)]

theorem length_encode {n : ℕ} (F : CNF n) :
    (encodeSet n F).length = Encoding.formulaBitLength (toOAI F) := by
  rw [encode_eq]; rfl

end ETHIsFalse.Proof
