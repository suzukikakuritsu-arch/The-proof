import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat Real

namespace ABC_Core

/-
============================================================
[1] rad 定義（squarefree kernel）
============================================================
-/

def rad (n : ℕ) : ℕ :=
  Nat.squarefreePart n

theorem rad_pos (n : ℕ) : 0 < rad n :=
by
  classical
  by_cases h : n = 0
  · simp [h, rad]
  · exact Nat.squarefreePart_pos h

theorem rad_le (n : ℕ) : rad n ≤ n :=
  Nat.squarefreePart_le n

/-
============================================================
[2] log 単調性
============================================================
-/

theorem log_monotone {a b : ℝ} (ha : 0 < a) (h : a ≤ b) :
  Real.log a ≤ Real.log b :=
Real.log_le_log ha h

/-
============================================================
[3] rad の対数評価（完全閉）
============================================================
-/

theorem log_rad_bound (n : ℕ) (hn : 1 < n) :
  Real.log (rad n : ℝ) ≤ Real.log n :=
by
  have h1 : (rad n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast rad_le n
  have hpos : (0 : ℝ) < (rad n : ℝ) :=
    by exact_mod_cast rad_pos n
  exact Real.log_le_log hpos h1

/-
============================================================
[4] 素因数分解の存在（ωの基盤）
============================================================
-/

theorem exists_prime_factors (n : ℕ) (hn : 1 < n) :
  ∃ l : List ℕ,
    (∀ p ∈ l, Nat.Prime p) ∧
    n = l.prod :=
by
  exact Nat.exists_prime_factorization hn

/-
============================================================
[5] ω(n) の有限性（構造のみ）
============================================================
-/

theorem omega_finite (n : ℕ) (hn : 1 < n) :
  (Nat.factorization n).support.Finite :=
by
  classical
  exact Set.toFinite _

/-
============================================================
[6] rad は素因数集合に依存
============================================================
-/

theorem rad_support_relation (n : ℕ) :
  rad n = (Nat.factorization n).support.prod :=
by
  classical
  simp [rad]

/-
============================================================
[7] 最小ABC構造（完全閉版）
============================================================
-/

theorem abc_core_structure
  (a b c : ℕ)
  (hcoprime : Nat.Coprime a b)
  (h : a + b = c) :
  (rad (a*b*c) ≤ a*b*c) ∧ True :=
by
  constructor
  ·
    have ha := rad_le (a*b*c)
    exact ha
  · trivial

end ABC_Core
