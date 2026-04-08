import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

open Real

namespace Pillai

/-- log(1+t) の基本評価（小さい領域） -/
lemma log_one_add_bound
  (t : ℝ) (ht : |t| ≤ (1 / 2 : ℝ)) :
  |log (1 + t)| ≤ 2 * |t| :=
by
  -- Mathlibに近い補題があるが、ここでは明示的に使う形
  have h₁ : |t| < 1 := by
    have : (1 / 2 : ℝ) < 1 := by norm_num
    exact lt_of_le_of_lt ht this

  -- log(1+t) のテイラー評価に基づく標準結果
  -- （Mathlib: abs_log_one_add_le_iff などで代替可能）
  have : |log (1 + t)| ≤ |t| / (1 - |t|) :=
    abs_log_one_add_le_abs_self_div_one_sub_abs_self h₁

  -- |t| ≤ 1/2 → 1/(1-|t|) ≤ 2
  have h₂ : 1 / (1 - |t|) ≤ 2 := by
    have hpos : 0 < 1 - |t| := by
      have : |t| < 1 := h₁
      linarith
    have : (1 : ℝ) ≤ 2 * (1 - |t|) := by
      have : |t| ≤ 1/2 := ht
      linarith
    field_simp [hpos] at this
    exact this

  -- 合成
  have := mul_le_mul_of_nonneg_left h₂ (abs_nonneg t)
  have := le_trans this this
  linarith


/-- 核心：log差の上界（完全版） -/
lemma log_diff_upper_strict
  (x y p q : ℕ) (k : ℤ)
  (hx : 2 ≤ x) (hy : 2 ≤ y)
  (h : (x:ℤ)^p - (y:ℤ)^q = k)
  (hsmall : |(k : ℝ)| / (y : ℝ) ^ (q : ℝ) ≤ (1 / 2 : ℝ)) :
  |(p : ℝ) * log x - (q : ℝ) * log y|
    ≤ 2 * |(k : ℝ)| * (y : ℝ) ^ (-(q : ℝ)) :=
by
  -- Step 1: 変形
  have hpos : (y : ℝ) ^ (q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hy)
    exact pow_ne_zero _ (ne_of_gt this)

  -- x^p = y^q + k
  have hxpy :
    (x : ℝ) ^ (p : ℝ)
      = (y : ℝ) ^ (q : ℝ) + (k : ℝ) := by
    exact_mod_cast h

  -- 比に変換
  have hratio :
    (x : ℝ) ^ (p : ℝ) / (y : ℝ) ^ (q : ℝ)
      = 1 + (k : ℝ) / (y : ℝ) ^ (q : ℝ) := by
    field_simp [hxpy, hpos]

  -- logを取る
  have hlog :
    (p : ℝ) * log x - (q : ℝ) * log y
      = log (1 + (k : ℝ) / (y : ℝ) ^ (q : ℝ)) := by
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hx)
    have hypos : 0 < (y : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hy)

    have := log_div ((x : ℝ) ^ (p : ℝ)) ((y : ℝ) ^ (q : ℝ))
    simp [log_pow, hxpos, hypos] at this
    simpa [hratio] using this

  -- Step 2: t の定義
  set t := (k : ℝ) / (y : ℝ) ^ (q : ℝ)

  have ht : |t| ≤ (1 / 2 : ℝ) := by
    simpa [t]

  -- Step 3: log評価
  have hbound := log_one_add_bound t ht

  -- Step 4: 展開
  have :
    |(p : ℝ) * log x - (q : ℝ) * log y|
      = |log (1 + t)| := by
    simpa [t] using congrArg abs hlog

  -- Step 5: 最終評価
  have :
    |(p : ℝ) * log x - (q : ℝ) * log y|
      ≤ 2 * |t| := by
    simpa [this] using hbound

  -- t戻す
  simpa [t, abs_div, pow_neg] using this


end Pillai
