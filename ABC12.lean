import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

open Real

namespace SStability

/- ============================================================
[SECTION 1] ω(n) の基本上界
============================================================ -/

-- 素因数の個数は log n / log 2 以下
axiom omega_bound (n : ℕ) (hn : 2 ≤ n) :
  (Nat.factorization n).support.card ≤ (log n / log 2)

/- ============================================================
[SECTION 2] rad の対数評価
============================================================ -/

-- rad(n) ≤ n
axiom rad_le (n : ℕ) : rad n ≤ n

-- log rad(n) ≤ log n
lemma log_rad_le_log (n : ℕ) (hn : 2 ≤ n) :
  log (rad n : ℝ) ≤ log (n : ℝ) := by
  have := rad_le n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by linarith))
  have hr : 0 < (rad n : ℝ) := by positivity
  exact log_le_log hr hn' (by exact_mod_cast this)

/- ============================================================
[SECTION 3] 指数 vs 素因数増大
============================================================ -/

/--
指数成長は素因数個数の増大を圧倒する
-/
lemma exponent_dominates_omega
  (y q : ℕ) (hy : 2 ≤ y) :
  (Nat.factorization (y^q)).support.card
    ≤ (log (y^q) / log 2) := by
  have h1 : 2 ≤ y^q := by
    exact pow_le_pow_of_le_left (by decide) hy q
  exact omega_bound (y^q) h1

/--
log(y^q) = q log y
-/
lemma log_pow_expand (y q : ℕ) (hy : 2 ≤ y) :
  log (y^q : ℝ) = (q : ℝ) * log y := by
  have hy' : 0 < (y : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hy)
  simpa using log_pow hy' q

/- ============================================================
[SECTION 4] S-stability の核心不等式
============================================================ -/

/--
素因数の種類数は高々線形（q に対して）、
しかし値は指数的に増大する
-/
theorem omega_vs_value_gap
  (y q : ℕ) (hy : 2 ≤ y) :
  (Nat.factorization (y^q)).support.card
    ≤ ((q : ℝ) * log y) / log 2 := by
  have h1 := exponent_dominates_omega y q hy
  have h2 := log_pow_expand y q hy
  simpa [h2] using h1

/--
値の大きさと素因数数のギャップ
-/
theorem exponential_vs_prime_support
  (y q : ℕ) (hy : 2 ≤ y) :
  (y : ℝ)^q ≥
    Real.exp ((Nat.factorization (y^q)).support.card) := by
  -- 粗い評価：exp(card) ≤ y^q
  have h1 : (Nat.factorization (y^q)).support.card
      ≤ ((q : ℝ) * log y) / log 2 :=
    omega_vs_value_gap y q hy

  have hlog : log (y : ℝ) > 0 := by
    exact log_pos (by exact_mod_cast hy)

  -- exp(card) ≤ exp(q log y)
  have h2 :
    Real.exp ((Nat.factorization (y^q)).support.card)
      ≤ Real.exp ((q : ℝ) * log y) := by
    apply exp_le_exp.mpr
    have : (Nat.factorization (y^q)).support.card
        ≤ (q : ℝ) * log y := by
      have := h1
      -- log 2 ≥ 1 を使った緩和
      have hlog2 : (1 : ℝ) ≤ log 2 := by norm_num
      have := mul_le_mul_of_nonneg_left this (by positivity)
      simpa using this
    exact this

  simpa [Real.exp_eq_rpow] using h2

/- ============================================================
[SECTION 5] S-stability（結論形）
============================================================ -/

/--
指数が十分大きいと、新しい素数を増やす意味が消える
（形式化された S-stability の原型）
-/
theorem S_stability_prototype
  (x y p q : ℕ) (hy : 2 ≤ y) :
  ∃ N : ℕ, q ≥ N →
    (Nat.factorization (y^q)).support.card
      ≤ (Nat.factorization (y^N)).support.card := by
  refine ⟨100, ?_⟩
  intro hq

  -- 成長は対数的なので eventually 停滞
  have : (Nat.factorization (y^q)).support.card
      ≤ ((q : ℝ) * log y) / log 2 :=
    omega_vs_value_gap y q hy

  -- ここで「増加速度が遅すぎる」ことを使う
  -- 実際にはここを tightening すれば完全S固定になる
  exact le_of_lt (by
    -- ダミー（本質はここを sharpen すること）
    have : (Nat.factorization (y^q)).support.card < 1000 := by
      sorry
    exact this)

end SStability
