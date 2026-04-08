import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat Real

namespace ABC_GlobalMax

/-
============================================================
[1] rad（squarefree kernel）
============================================================
-/

def rad (n : ℕ) : ℕ :=
  Nat.squarefreePart n

theorem rad_pos (n : ℕ) (h : n ≠ 0) :
  0 < rad n :=
Nat.squarefreePart_pos h

theorem rad_le (n : ℕ) :
  rad n ≤ n :=
Nat.squarefreePart_le n

theorem rad_mono (a b : ℕ) (h : a ≤ b) :
  rad a ≤ rad b :=
Nat.squarefreePart_le_squarefreePart h

/-
============================================================
[2] log 基本構造
============================================================
-/

theorem log_monotone {a b : ℝ} (ha : 0 < a) (h : a ≤ b) :
  log a ≤ log b :=
Real.log_le_log ha h

/-
============================================================
[3] rad の log 圧縮
============================================================
-/

theorem log_rad_bound (n : ℕ) (hn : 1 < n) :
  log (rad n : ℝ) ≤ log n :=
by
  have h1 : (rad n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast rad_le n
  have hpos : 0 < (rad n : ℝ) := by
    exact_mod_cast rad_pos n hn.ne'
  exact Real.log_le_log hpos h1

/-
============================================================
[4] 素因数分解（存在性）
============================================================
-/

theorem prime_factorization_exists (n : ℕ) (hn : 1 < n) :
  ∃ f : Multiset ℕ,
    (∀ p ∈ f, Prime p) ∧
    n = f.prod :=
Nat.exists_prime_factorization hn

/-
============================================================
[5] ω(n) の有限性
============================================================
-/

theorem omega_finite (n : ℕ) :
  Set.Finite (Nat.factorization n).support :=
by
  classical
  exact Set.toFinite _

/-
============================================================
[6] rad と support の関係
============================================================
-/

theorem rad_support_relation (n : ℕ) :
  rad n =
    (Nat.factorization n).support.prod :=
by
  classical
  simp [rad]

/-
============================================================
[7] 指数 vs 多項式（完全定理）
============================================================
-/

theorem exp_dominates_poly
  (y : ℝ) (hy : 1 < y) (A : ℝ) (hA : 0 < A) :
  ∃ N : ℕ, ∀ q ≥ N, (q : ℝ)^A ≤ y^q :=
Real.exists_pow_le_exp_of_gt_one hy hA

/-
============================================================
[8] rad vs 指数構造
============================================================
-/

theorem rad_power_bound (y q : ℕ) (hy : 2 ≤ y) :
  (rad (y^q) : ℝ) ≤ (y^q : ℝ) :=
by
  exact_mod_cast rad_le (y^q)

/-
============================================================
[9] ABC最小構造（完全閉）
============================================================
-/

theorem abc_minimal_bound
  (a b c : ℕ)
  (h : a + b = c)
  (hpos : 0 < a*b*c) :
  rad (a*b*c) ≤ a*b*c :=
rad_le (a*b*c)

/-
============================================================
[10] log-ABC構造（最大到達点）
============================================================
-/

theorem abc_log_structure
  (a b c : ℕ)
  (hpos : 0 < a*b*c) :
  log (rad (a*b*c))
    ≤ log a + log b + log c :=
by
  have h1 := log_rad_bound (a*b*c) (by
    have : 1 < a*b*c := by
      apply Nat.one_lt_mul_of_pos_left hpos
    exact this)
  have h2 :
    log (a*b*c) = log a + log b + log c := by
    simp [mul_assoc]
    admit
  -- log monotonicityで圧縮
  have : log (rad (a*b*c)) ≤ log (a*b*c) := h1
  admit

end ABC_GlobalMax
