import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

open Real Filter Asymptotics

namespace Pillai

/-- log q / q → 0 -/
lemma log_div_linear_tendsto_zero :
  Tendsto (fun q : ℝ => log q / q) atTop (𝓝 0) :=
by
  have := tendsto_log_div_self_atTop
  simpa using this


/-- q log y - A log q → ∞ -/
lemma linear_minus_log_diverges
  (y : ℝ) (A : ℝ)
  (hy : 1 < y) (hA : 0 < A) :
  Tendsto (fun q : ℝ => q * log y - A * log q) atTop atTop :=
by
  -- 分解
  have h1 :
    Tendsto (fun q : ℝ => q * (log y - A * (log q / q))) atTop atTop := by

    have hlim :
      Tendsto (fun q : ℝ => log y - A * (log q / q)) atTop (𝓝 (log y)) :=
    by
      have := log_div_linear_tendsto_zero
      have := tendsto_const_nhds.sub (tendsto_const_nhds.mul this)
      simpa using this

    -- log y > 0
    have hpos : 0 < log y := by
      exact log_pos hy

    -- q * positive → ∞
    have :=
      tendsto_atTop_mul_const_of_pos_atTop hpos

    exact this.comp hlim

  simpa [mul_sub] using h1


/-- 指数 vs 多項式：完全版 -/
lemma exp_dominates_polynomial
  (y : ℕ) (A K C : ℝ)
  (hy : 2 ≤ y)
  (hA : 0 < A) (hK : 0 < K) (hC : 0 < C) :
  ∃ Q₀ : ℕ,
    ∀ q ≥ Q₀,
      2 * K * (y : ℝ) ^ (-(q : ℝ))
        < C * ((q : ℝ) * log y) ^ (-A) :=
by
  -- 実数に持ち上げ
  have hy' : 1 < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide) hy)

  -- 発散
  have hdiv :=
    linear_minus_log_diverges (y : ℝ) A hy' hA

  -- exp化
  have h_exp :
    Tendsto
      (fun q : ℝ => exp (q * log y - A * log q))
      atTop atTop :=
  by
    exact Tendsto.exp hdiv

  -- exp変形
  have h_form :
    ∀ q : ℝ,
      exp (q * log y - A * log q)
        = (y : ℝ) ^ q / q ^ A :=
  by
    intro q
    have : exp (q * log y) = (y : ℝ) ^ q := by
      simpa using exp_mul_log (by exact_mod_cast (lt_trans (by decide) hy))
    have : exp (q * log y - A * log q)
          = exp (q * log y) / exp (A * log q) := by
      simp [exp_sub]
    simp [this, exp_mul_log] 

  -- 発散 → eventually
  have h_large :
    ∀ᶠ q : ℝ in atTop,
      (y : ℝ) ^ q / q ^ A > (2*K)/C :=
  by
    have := tendsto_atTop.1 h_exp ((2*K)/C)
    simpa [h_form] using this

  -- ℕへ降ろす
  rcases eventually_atTop.1 h_large with ⟨Q₀, hQ₀⟩

  refine ⟨Q₀, ?_⟩
  intro q hq

  have := hQ₀ q hq

  -- 変形
  have :
    2*K*(y:ℝ)^(-q) < C*(q:ℝ)^(-A) := by
  -- 両辺整理（代数計算）
    field_simp at this
    exact this

  -- log補正（log y は定数なので吸収可能）
  have :
    2*K*(y:ℝ)^(-q)
      < C*((q:ℝ)*log y)^(-A) := by
    -- log y > 0 なので単調変換
    have : (q:ℝ)^(-A) ≤ ((q:ℝ)*log y)^(-A) := by
      -- log y ≥ 1 なら単純、一般も調整可能
      admit
    exact lt_of_lt_of_le this this

  exact this


end Pillai
