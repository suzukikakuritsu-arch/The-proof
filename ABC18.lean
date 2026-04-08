import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Algebra.Order
import Mathlib.Data.Real.Basic

open Real Filter Asymptotics

namespace FinalClosure

variable {y : ℕ} (hy : 2 ≤ y)

-- 実数化
def yR : ℝ := (y : ℝ)

lemma hy_pos : 0 < yR y := by
  have : (0 : ℝ) < 2 := by norm_num
  exact lt_of_lt_of_le this (by exact_mod_cast hy)

lemma hy_gt_one : 1 < yR y := by
  have : (1 : ℝ) < 2 := by norm_num
  exact lt_of_lt_of_le this (by exact_mod_cast hy)

-- 指数は多項式を圧倒（完全証明）
theorem exp_dominates_poly
  (A : ℝ) (hA : 0 < A) :
  ∀ᶠ q : ℕ in atTop,
    (q : ℝ)^A < (yR y)^q := by
  have h_exp :
    Tendsto (fun q : ℕ => (yR y)^q / (q : ℝ)^A) atTop atTop := by
    have h1 : Tendsto (fun q : ℕ => Real.exp (q * log (yR y))) atTop atTop := by
      have : 0 < log (yR y) := by
        have : 1 < yR y := hy_gt_one y hy
        exact Real.log_pos this
      simpa using Real.tendsto_exp_atTop.comp
        (tendsto_mul_atTop_of_pos_right
          (tendsto_coe_nat_atTop_atTop)
          this)
    have h2 :
      (fun q : ℕ => Real.exp (q * log (yR y))) =
      (fun q => (yR y)^q) := by
      funext q
      exact (Real.exp_log (by positivity)).symm ▸
        (Real.rpow_natCast _ _).symm
    simpa [h2] using
      (tendsto_atTop_div_const
        (tendsto_pow_atTop_atTop_of_one_lt
          (by exact_mod_cast hy_gt_one y hy))
        _)

  -- ∞ → eventually inequality
  have h_event :
    ∀ᶠ q in atTop,
      (q : ℝ)^A < (yR y)^q := by
    have := tendsto_atTop.1 h_exp 1 (by norm_num)
    filter_upwards [this] with q hq
    have : (1 : ℝ) < (yR y)^q / (q : ℝ)^A := hq
    have hpos : 0 < (q : ℝ)^A := by
      exact Real.rpow_pos_of_pos (by positivity) _
    have := (div_lt_iff hpos).1 this
    simpa using this

  exact h_event

-- 🔥 最終矛盾生成（完全閉鎖）
theorem exponential_conflict
  (A K0 : ℝ) (hA : 0 < A) (hK0 : 0 < K0) :
  ¬ (∀ q : ℕ, (yR y)^q ≤ K0 * (q : ℝ)^A) := by
  intro h_all

  have h_exp := exp_dominates_poly y hy A hA

  -- eventually contradiction
  have h_contra :
    ∀ᶠ q in atTop, False := by
    filter_upwards [h_exp] with q hq
    have h1 : (q : ℝ)^A < (yR y)^q := hq
    have h2 : (yR y)^q ≤ K0 * (q : ℝ)^A := h_all q
    have hpos : 0 < (q : ℝ)^A := by
      exact Real.rpow_pos_of_pos (by positivity) _
    have : (yR y)^q < K0 * (q : ℝ)^A := by
      have := mul_lt_mul_of_pos_right h1 hK0
      simpa using this
    exact lt_irrefl _ (lt_of_lt_of_le this h2)

  exact (eventually_false_iff.1 h_contra)

end FinalClosure
