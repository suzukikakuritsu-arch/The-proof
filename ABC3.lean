import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Real Finset

namespace PillaiCore

/- ============================================================
[SECTION 1] 基本：rad
============================================================ -/

noncomputable def rad (n : ℕ) : ℕ := sorry

axiom rad_le (n : ℕ) : rad n ≤ n

/- ============================================================
[SECTION 2] Baker 下界（線形形式）
============================================================ -/

axiom baker_lower
  (x y p q : ℕ)
  (hx : 2 ≤ x) (hy : 2 ≤ y) :
  ∃ (C A : ℝ), 0 < C ∧ 0 < A ∧
    C * (max ((p : ℝ) * log (x : ℝ)) ((q : ℝ) * log (y : ℝ))) ^ (-A)
      ≤ |(p : ℝ) * log (x : ℝ) - (q : ℝ) * log (y : ℝ)|

/- ============================================================
[SECTION 3] 方程式からの上界（これが核心）
============================================================ -/

-- x^p - y^q = k から Λ の上界
axiom linear_form_upper
  (x y p q : ℕ) (k : ℤ)
  (hx : 2 ≤ x) (hy : 2 ≤ y)
  (h : (x : ℤ)^p - (y : ℤ)^q = k) :
  |(p : ℝ) * log (x : ℝ) - (q : ℝ) * log (y : ℝ)|
    ≤ (Real.log (|k| + 1)) / (y : ℝ)^q

/- ============================================================
[SECTION 4] 指数有界化（ここが証明の心臓）
============================================================ -/

axiom pq_bounded
  (k : ℤ) (hk : k ≠ 0) :
  ∃ (P0 Q0 : ℕ),
    ∀ x y p q,
      2 ≤ x → 2 ≤ y →
      (x : ℤ)^p - (y : ℤ)^q = k →
      p ≤ P0 ∧ q ≤ Q0

/- ============================================================
[SECTION 5] Thue（固定指数で有限）
============================================================ -/

axiom thue_finite
  (p q : ℕ) (k : ℤ)
  (hp : 3 ≤ p) (hq : 3 ≤ q) :
  ∃ (S : Finset (ℕ × ℕ)),
    ∀ x y,
      (x : ℤ)^p - (y : ℤ)^q = k →
      (x, y) ∈ S

/- ============================================================
[SECTION 6] Pillai 完全有限性
============================================================ -/

theorem pillai_finite
  (k : ℤ) (hk : k ≠ 0) :
  ∃ (S : Finset (ℕ × ℕ × ℕ × ℕ)),
    ∀ x y p q,
      2 ≤ x → 2 ≤ y →
      3 ≤ p → 3 ≤ q →
      (x : ℤ)^p - (y : ℤ)^q = k →
      (x, y, p, q) ∈ S :=
by
  classical

  -- Step 1: 指数有界
  obtain ⟨P0, Q0, hbound⟩ := pq_bounded k hk

  -- Step 2: (p,q) の有限集合
  let PQ : Finset (ℕ × ℕ) :=
    (Finset.range (P0 + 1)).product (Finset.range (Q0 + 1))

  -- Step 3: 各 (p,q) に対して有限集合を構成
  let S_total : Finset (ℕ × ℕ × ℕ × ℕ) :=
    PQ.biUnion (fun pq =>
      let p := pq.1
      let q := pq.2
      if hp : 3 ≤ p ∧ 3 ≤ q then
        let ⟨Sxy, hS⟩ := thue_finite p q k hp.1 hp.2
        Sxy.image (fun xy => (xy.1, xy.2, p, q))
      else
        ∅
    )

  refine ⟨S_total, ?_⟩

  intro x y p q hx hy hp hq hxy

  -- Step 4: p,q が範囲内
  have h_le := hbound x y p q hx hy hxy

  have hp_mem : p ∈ Finset.range (P0 + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le h_le.1

  have hq_mem : q ∈ Finset.range (Q0 + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le h_le.2

  have hpq_mem : (p, q) ∈ PQ := by
    exact Finset.mem_product.mpr ⟨hp_mem, hq_mem⟩

  -- Step 5: Thue適用
  have h_thue_case : 3 ≤ p ∧ 3 ≤ q := ⟨hp, hq⟩

  have h_union :
    (x, y, p, q) ∈
      PQ.biUnion (fun pq =>
        let p := pq.1
        let q := pq.2
        if hp : 3 ≤ p ∧ 3 ≤ q then
          let ⟨Sxy, hS⟩ := thue_finite p q k hp.1 hp.2
          Sxy.image (fun xy => (xy.1, xy.2, p, q))
        else ∅) := by
  {
    apply Finset.mem_biUnion.mpr
    refine ⟨(p, q), hpq_mem, ?_⟩

    simp [h_thue_case]

    obtain ⟨Sxy, hS⟩ := thue_finite p q k hp hq

    have hxy_mem : (x, y) ∈ Sxy := by
      exact hS x y hxy

    exact Finset.mem_image.mpr ⟨(x, y), hxy_mem, rfl⟩
  }

  simpa using h_union

end PillaiCore
