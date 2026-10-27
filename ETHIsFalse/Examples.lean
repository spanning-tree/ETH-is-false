import ETHIsFalse.Statement

/-! The examples in the comments of `Statement.lean`, checked by Lean (`decide` evaluates in the
kernel; `#guard` runs the compiled code, for the two that go through `Finset.sort`). -/

namespace ETHIsFalse

example : unary 2 = [true, true, false] := by decide
example : frame [true, false] = [true, true, true, false, false] := by decide
example : listCode unary [0, 1] =
    [true, true, false, false, true, true, true, true, false, false, false] := by decide
#guard clauseNumbers ({(1, false), (0, true)} : Finset (Fin 2 × Bool)) == [1, 2]
example : clauseSet (⟨#[[(0, true)], [(1, false), (0, true)], [(0, true), (0, true)]]⟩ :
    Std.Sat.CNF (Fin 2)) = {{(0, true)}, {(0, true), (1, false)}} := by decide
example : listCode unary [1] = [true, true, true, true, false, false, false] := by decide
example : listCode unary [1, 2] = [true, true, true, true, false, false,
    true, true, true, true, true, true, false, false, false] := by decide
#guard encode 2 (⟨#[[(0, true)], [(1, false), (0, true)]]⟩ : Std.Sat.CNF (Fin 2)) ==
    unary 2 ++ listCode (listCode unary) [[1], [1, 2]]
example : binary 6 = [false, true, true] := by decide
example : binary 0 = [false] := by decide

end ETHIsFalse
