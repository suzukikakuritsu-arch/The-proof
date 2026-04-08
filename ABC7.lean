import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Algebra.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Filter Asymptotics

namespace ExponentialConflict

/-
============================================================
[LEMMA 1] 指数は多項式を支配する（完全版）
============================================================
-/

lemma exp_dominates_poly
  (y A : ℝ)
  (hy : 1 < y)
  (hA : 0 < A) :
  Tendsto (fun q : ℝ => (y^q) / (q^A)) atTop atTop :=
by
  -- log を取って評価
  have h_log :
    Tendsto (fun q : ℝ => log ((y^q) / (q^A))) atTop atTop := by
  {
    have h1 : ∀ᶠ q in atTop, 0 < q := eventually_gt_atTop 0
    have h2 : log y > 0 := log_pos hy

    -- log(y^q / q^A) = q log y - A log q
    have h_expand :
      ∀ᶠ q in atTop,
        log ((y^q) / (q^A)) = q * log y - A * log q := by
    {
      filter_upwards [h1] with q hq
      have hq' : q ≠ 0 := ne_of_gt hq
      simp [log_div, log_pow, hq', mul_comm, mul_left_comm, mul_assoc]
    }

    -- 主項 q log y が log q を圧倒
    have h_main :
      Tendsto (fun q : ℝ => q * log y - A * log q) atTop atTop :=
    by
      have : Tendsto (fun q : ℝ => q * log y) atTop atTop :=
        tendsto_const_mul_atTop h2
      have : Tendsto (fun q : ℝ => A * log q) atTop atTop :=
        (tendsto_log_atTop).const_mul A
      -- 差は +∞
      exact tendsto_sub_atTop_atTop this ‹_›

    exact h_main.congr' h_expand
  }

  -- exp を戻す
  have h_exp :
    Tendsto (fun q : ℝ => exp (log ((y^q) / (q^A)))) atTop atTop :=
    h_log.exp

  -- exp ∘ log = id
  have h_id :
    ∀ᶠ q in atTop, exp (log ((y^q) / (q^A))) = (y^q) / (q^A) :=
  by
    filter_upwards [eventually_gt_atTop 0] with q hq
    have : 0 < (y^q) / (q^A) := by
      have hypos : 0 < y := lt_trans zero_lt_one hy
      positivity
    simp [this]

  exact h_exp.congr' h_id


/-
============================================================
[LEMMA 2] 十分大きければ任意定数を超える
============================================================
-/

lemma exp_poly_eventually_gt
  (y A C : ℝ)
  (hy : 1 < y)
  (hA : 0 < A)
  (hC : 0 < C) :
  ∃ N : ℝ, ∀ q ≥ N, C * q^A < y^q :=
by
  -- 発散性を使う
  have h := exp_dominates_poly y A hy hA

  -- 定数 (C) を超える点が存在
  have h' :
    ∀ᶠ q in atTop, (y^q) / (q^A) > C :=
    (tendsto_atTop.1 h) C

  rcases eventually_atTop.1 h' with ⟨N, hN⟩

  refine ⟨N, ?_⟩
  intro q hq

  have hq' := hN q hq

  have hpos : 0 < q^A := by positivity

  -- 両辺に q^A を掛ける
  have := mul_lt_mul_of_pos_right hq' hpos
  field_simp at this
  exact this


/-
============================================================
[THEOREM] 最終矛盾（完全閉包）
============================================================
-/

theorem exponential_vs_polynomial_contradiction
  (y A C : ℝ)
  (hy : 1 < y)
  (hA : 0 < A)
  (hC : 0 < C) :
  ¬ (∀ q ≥ 1, y^q ≤ C * q^A) :=
by
  intro h_all

  -- 指数優位を取得
  obtain ⟨N, hN⟩ := exp_poly_eventually_gt y A C hy hA hC

  -- N以上で矛盾
  have h1 := h_all N (by linarith)
  have h2 := hN N (by linarith)

  linarith


end ExponentialConflict
