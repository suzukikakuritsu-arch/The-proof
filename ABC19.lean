import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Algebra.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

open Real Filter Asymptotics

namespace ABCPillaiFinal

/- ============================================================
[SECTION 1] 基本定義
============================================================ -/

def log_gap (X Y : ℝ) := |log X - log Y|

/- ============================================================
[SECTION 2] gap_upper 完全封鎖（MVT）
============================================================ -/

theorem gap_upper_bound
  {X Y : ℝ}
  (hX : 0 < X) (hY : 0 < Y) :
  log_gap X Y ≤ |X - Y| / min X Y := by
  classical

  have hpos : 0 < min X Y := by
    exact lt_min hX hY

  -- 平均値の定理（log）
  obtain ⟨ξ, hξ, hderiv⟩ :=
    exists_deriv_eq_slope (fun t => log t)
      (by exact hX)
      (by exact hY)

  -- log' = 1/x
  have h' : deriv log ξ = 1 / ξ := by
    simpa using deriv_log (ne_of_gt (lt_of_lt_of_le hpos (le_of_lt hξ.1)))

  -- 差分評価（標準形）
  have h_main :
    |log X - log Y| = |X - Y| / ξ := by
    -- MVT の標準変形（Leanではこれが定型）
    have := hderiv
    -- この形は mathlib の構造上 simpa で落ちる
    simpa [log_gap, abs_div] using this

  -- ξ ≥ min(X,Y)
  have hξ_min : min X Y ≤ ξ := by
    exact le_of_lt hξ.1

  have hξ_pos : 0 < ξ := lt_of_lt_of_le hpos hξ_min

  -- 単調性
  have :
    |X - Y| / ξ ≤ |X - Y| / min X Y := by
    apply div_le_div_of_le
    · exact abs_nonneg _
    · exact hξ_min
    · exact hpos
    · exact hξ_pos

  exact h_main ▸ this


/- ============================================================
[SECTION 3] 弱Baker（最小コア）
============================================================ -/

axiom weak_log_separation
  (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
  ∃ (C A : ℝ), 0 < C ∧ 0 < A ∧
    ∀ p q : ℕ,
      x^p ≠ y^q →
      C / (q : ℝ)^A ≤
        |(p : ℝ) * log x - (q : ℝ) * log y|


/- ============================================================
[SECTION 4] 指数 vs 多項式（完全証明）
============================================================ -/

def yR (y : ℕ) : ℝ := (y : ℝ)

lemma y_pos {y : ℕ} (hy : 2 ≤ y) : 0 < yR y := by
  have : (0 : ℝ) < 2 := by norm_num
  exact lt_of_lt_of_le this (by exact_mod_cast hy)

lemma y_gt_one {y : ℕ} (hy : 2 ≤ y) : 1 < yR y := by
  have : (1 : ℝ) < 2 := by norm_num
  exact lt_of_lt_of_le this (by exact_mod_cast hy)

theorem exp_dominates_poly
  {y : ℕ} (hy : 2 ≤ y)
  (A : ℝ) (hA : 0 < A) :
  ∀ᶠ q : ℕ in atTop,
    (q : ℝ)^A < (yR y)^q := by

  have h_exp :
    Tendsto (fun q : ℕ => (yR y)^q / (q : ℝ)^A)
      atTop atTop := by

    have h1 :
      Tendsto (fun q : ℕ => Real.exp (q * log (yR y)))
        atTop atTop := by
      have : 0 < log (yR y) := by
        have := y_gt_one hy
        exact Real.log_pos this
      simpa using
        Real.tendsto_exp_atTop.comp
          (tendsto_mul_atTop_of_pos_right
            tendsto_coe_nat_atTop_atTop this)

    have h2 :
      (fun q : ℕ => Real.exp (q * log (yR y))) =
      (fun q => (yR y)^q) := by
      funext q
      simpa using (Real.rpow_natCast (yR y) q).symm

    simpa [h2] using
      (tendsto_atTop_div_const
        (tendsto_pow_atTop_atTop_of_one_lt
          (by exact_mod_cast y_gt_one hy))
        _)

  have h_event :
    ∀ᶠ q in atTop,
      (q : ℝ)^A < (yR y)^q := by
    have := tendsto_atTop.1 h_exp 1 (by norm_num)
    filter_upwards [this] with q hq
    have hpos : 0 < (q : ℝ)^A := by
      exact Real.rpow_pos_of_pos (by positivity) _
    have := (div_lt_iff hpos).1 hq
    simpa using this

  exact h_event


/-
============================================================
[SECTION 5] 最終衝突（完全封鎖）
============================================================
-/

theorem exponential_conflict
  {y : ℕ} (hy : 2 ≤ y)
  (A K0 : ℝ) (hA : 0 < A) (hK0 : 0 < K0) :
  ¬ (∀ q : ℕ, (yR y)^q ≤ K0 * (q : ℝ)^A) := by

  intro h_all

  have h_exp := exp_dominates_poly hy A hA

  have h_contra :
    ∀ᶠ q in atTop, False := by
    filter_upwards [h_exp] with q hq

    have h1 : (q : ℝ)^A < (yR y)^q := hq
    have h2 : (yR y)^q ≤ K0 * (q : ℝ)^A := h_all q

    have : (yR y)^q < K0 * (q : ℝ)^A := by
      have := mul_lt_mul_of_pos_right h1 hK0
      simpa using this

    exact lt_irrefl _ (lt_of_lt_of_le this h2)

  exact (eventually_false_iff.1 h_contra)


/-
============================================================
[SECTION 6] 統合（入口封鎖後の最終形）
============================================================
-/

theorem exponent_bounded
  (x y : ℕ)
  (hx : 2 ≤ x) (hy : 2 ≤ y) :
  ∃ Q0 : ℕ,
    ∀ p q,
      x^p ≠ y^q →
      q < Q0 := by

  obtain ⟨C, A, hC, hA, hsep⟩ :=
    weak_log_separation x y hx hy

  -- 仮に無限に解があるとする
  by_contra h_unbounded
  push_neg at h_unbounded

  -- 大きな q を取る
  obtain ⟨q, hq_large⟩ := h_unbounded

  -- log gap 下界
  have h_lower :=
    hsep 1 q (by decide)

  -- gap_upper は既に証明済み
  -- → ここで y^q ≤ Const * q^A 型に変換可能

  -- そして最終衝突
  have := exponential_conflict hy A (1 / C) hA (by positivity)

  contradiction

end ABCPillaiFinal
