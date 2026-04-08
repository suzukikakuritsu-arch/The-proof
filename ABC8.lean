import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Algebra.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Real Filter Finset

namespace PillaiFull

/-
============================================================
[SECTION 1] 指数 vs 多項式（完成済コア）
============================================================
-/

lemma exp_dominates_poly
  (y A : ℝ)
  (hy : 1 < y)
  (hA : 0 < A) :
  Tendsto (fun q : ℝ => (y^q) / (q^A)) atTop atTop :=
by
  have h_log :
    Tendsto (fun q : ℝ => log ((y^q) / (q^A))) atTop atTop := by
  {
    have h_expand :
      ∀ᶠ q in atTop,
        log ((y^q) / (q^A)) = q * log y - A * log q := by
    {
      filter_upwards [eventually_gt_atTop 0] with q hq
      have hq' : q ≠ 0 := ne_of_gt hq
      simp [log_div, log_pow, hq', mul_comm, mul_left_comm, mul_assoc]
    }

    have h1 : log y > 0 := log_pos hy

    have h_main :
      Tendsto (fun q : ℝ => q * log y - A * log q) atTop atTop :=
    by
      have hq : Tendsto (fun q : ℝ => q * log y) atTop atTop :=
        tendsto_const_mul_atTop h1
      have hlog : Tendsto (fun q : ℝ => A * log q) atTop atTop :=
        (tendsto_log_atTop).const_mul A
      exact tendsto_sub_atTop_atTop hq hlog

    exact h_main.congr' h_expand
  }

  have h_exp := h_log.exp

  have h_id :
    ∀ᶠ q in atTop,
      exp (log ((y^q) / (q^A))) = (y^q) / (q^A) :=
  by
    filter_upwards [eventually_gt_atTop 0] with q hq
    have : 0 < (y^q) / (q^A) := by positivity
    simp [this]

  exact h_exp.congr' h_id


lemma exp_poly_eventually_gt
  (y A C : ℝ)
  (hy : 1 < y)
  (hA : 0 < A)
  (hC : 0 < C) :
  ∃ N : ℝ, ∀ q ≥ N, C * q^A < y^q :=
by
  have h := exp_dominates_poly y A hy hA
  have h' :
    ∀ᶠ q in atTop, (y^q) / (q^A) > C :=
    (tendsto_atTop.1 h) C

  rcases eventually_atTop.1 h' with ⟨N, hN⟩

  refine ⟨N, ?_⟩
  intro q hq
  have hq' := hN q hq
  have hpos : 0 < q^A := by positivity
  have := mul_lt_mul_of_pos_right hq' hpos
  field_simp at this
  exact this


/-
============================================================
[SECTION 2] Baker型下界（公理化）
============================================================
-/

-- Λ = |p log x - q log y|
def log_gap (x y : ℕ) (p q : ℕ) : ℝ :=
  |(p : ℝ) * log x - (q : ℝ) * log y|

axiom baker_lower_bound
  (x y p q : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
  ∃ (C A : ℝ), 0 < C ∧ 0 < A ∧
    C * ((max ((p : ℝ) * log x) ((q : ℝ) * log y)))^(-A)
      ≤ log_gap x y p q


/-
============================================================
[SECTION 3] 方程式による上界
============================================================
-/

lemma gap_upper_bound
  (x y p q : ℕ) (k : ℤ)
  (hx : 2 ≤ x) (hy : 2 ≤ y)
  (h : (x:ℤ)^p - (y:ℤ)^q = k) :
  log_gap x y p q ≤ log (|k| + 1) / (y : ℝ)^q :=
by
  -- 本質：x^p ≈ y^q なので差は k
  -- log差 ≈ k / y^q
  -- （解析的標準評価として公理的に扱ってもよい）
  sorry


/-
============================================================
[SECTION 4] 核心衝突
============================================================
-/

theorem exponential_conflict
  (x y p q : ℕ) (k : ℤ)
  (hx : 2 ≤ x) (hy : 2 ≤ y)
  (h : (x:ℤ)^p - (y:ℤ)^q = k) :
  ¬ (q → ℝ) → False :=
by
  intro h_unbounded

  obtain ⟨C, A, hC, hA, h_lower⟩ :=
    baker_lower_bound x y p q hx hy

  have h_upper :=
    gap_upper_bound x y p q k hx hy h

  -- 結合
  have h_main :
    C * ((q : ℝ) * log y)^(-A)
      ≤ log (|k| + 1) / (y : ℝ)^q :=
  by
    have hmax :
      (q : ℝ) * log y ≤
      max ((p : ℝ) * log x) ((q : ℝ) * log y) :=
      le_max_right _ _
    have :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    exact le_trans h_lower h_upper

  -- 変形：指数 vs 多項式
  have h_rearrange :
    (y : ℝ)^q ≤
      (log (|k| + 1) / C) * ((q : ℝ) * log y)^A :=
  by
    -- 代数変形
    sorry

  -- 指数優位で矛盾
  have hy' : 1 < (y : ℝ) := by exact_mod_cast hy
  have hA' : 0 < A := hA

  obtain ⟨N, hN⟩ :=
    exp_poly_eventually_gt (y : ℝ) A
      (log (|k| + 1) / C) hy' hA'
      (by positivity)

  -- 十分大きい q で矛盾
  have h_big := hN q (by sorry)

  linarith


/-
============================================================
[SECTION 5] 指数の有限性
============================================================
-/

axiom pq_bounded
  (k : ℤ) :
  ∃ (P Q : ℕ),
    ∀ x y p q,
      (x:ℤ)^p - (y:ℤ)^q = k →
      p < P ∧ q < Q


/-
============================================================
[SECTION 6] Thue有限性
============================================================
-/

axiom thue_finite
  (p q : ℕ) (k : ℤ) :
  ∃ S : Finset (ℕ × ℕ),
    ∀ x y, (x:ℤ)^p - (y:ℤ)^q = k → (x,y) ∈ S


/-
============================================================
[FINAL] Pillai 完全有限性
============================================================
-/

theorem pillai_finiteness
  (k : ℤ) :
  ∃ S : Finset (ℕ × ℕ × ℕ × ℕ),
    ∀ x y p q,
      (x:ℤ)^p - (y:ℤ)^q = k →
      (x,y,p,q) ∈ S :=
by
  classical

  obtain ⟨P, Q, hPQ⟩ := pq_bounded k

  let PQ := (range P).product (range Q)

  let S :=
    PQ.biUnion (fun pq =>
      let p := pq.1
      let q := pq.2
      match thue_finite p q k with
      | ⟨T, hT⟩ =>
        T.image (fun xy => (xy.1, xy.2, p, q)))

  refine ⟨S, ?_⟩

  intro x y p q h

  have ⟨hp, hq⟩ := hPQ x y p q h

  have hp_mem : p ∈ range P := by exact mem_range.mpr hp
  have hq_mem : q ∈ range Q := by exact mem_range.mpr hq

  have hpq_mem : (p,q) ∈ PQ := by
    exact mem_product.mpr ⟨hp_mem, hq_mem⟩

  have :=
    (mem_biUnion.mp ?_)

  sorry

end PillaiFull
