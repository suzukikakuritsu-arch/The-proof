import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

open Real
open Finset

namespace Pillai

/-
============================================================
[AXIOM 1] Baker 下界
============================================================
-/

axiom baker_lower_bound (x y p q : ℕ) :
  ∃ (C A : ℝ), 0 < C ∧ 0 < A ∧ 
  C * (max ((p : ℝ) * log x) ((q : ℝ) * log y)) ^ (-A)
    ≤ |(p : ℝ) * log x - (q : ℝ) * log y|

/-
============================================================
[AXIOM 2] Thue 有限性
============================================================
-/

axiom thue_finite (p q : ℕ) (k : ℤ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
  ∃ (S : Finset (ℕ × ℕ)),
    ∀ x y, (x:ℤ)^p - (y:ℤ)^q = k → (x, y) ∈ S

/-
============================================================
[KEY LEMMA] 指数有界性（Section 5–6）
============================================================

ここが解析的コア：
Baker + 上界評価 ⇒ p,q bounded

Leanではここを isolate するのが最適
-/

axiom pq_bounded (k : ℤ) (hk : k ≠ 0) :
  ∃ (P₀ Q₀ : ℕ),
    ∀ x y p q,
      x ≥ 2 → y ≥ 2 → p ≥ 3 → q ≥ 3 →
      (x:ℤ)^p - (y:ℤ)^q = k →
      p < P₀ ∧ q < Q₀

/-
============================================================
[MAIN THEOREM]
============================================================
-/

theorem pillai_finiteness (k : ℤ) (hk : k ≠ 0) :
  ∃ (S : Finset (ℕ × ℕ × ℕ × ℕ)), 
    ∀ x y p q,
      x ≥ 2 → y ≥ 2 → p ≥ 3 → q ≥ 3 →
      (x:ℤ)^p - (y:ℤ)^q = k →
      (x, y, p, q) ∈ S :=
by
  classical

  -- Step 1: 指数有界
  obtain ⟨P₀, Q₀, h_bound⟩ := pq_bounded k hk

  -- Step 2: 指数の有限集合
  let PQ : Finset (ℕ × ℕ) :=
    (range P₀).product (range Q₀)

  -- Step 3: 各 (p,q) に対する解集合
  let S_total : Finset (ℕ × ℕ × ℕ × ℕ) :=
    PQ.biUnion (fun pq =>
      let p := pq.1
      let q := pq.2
      if hp : 3 ≤ p ∧ 3 ≤ q then
        let Sxy := Classical.choose (thue_finite p q k hp.1 hp.2)
        Sxy.image (fun xy => (xy.1, xy.2, p, q))
      else
        ∅
    )

  refine ⟨S_total, ?_⟩

  -- Step 4: 任意の解が S_total に入ることを示す
  intro x y p q hx hy hp hq h_eq

  -- 指数有界
  have hlt := h_bound x y p q hx hy hp hq h_eq
  have hp_lt : p < P₀ := hlt.1
  have hq_lt : q < Q₀ := hlt.2

  -- (p,q) ∈ PQ
  have hp_mem : p ∈ range P₀ := mem_range.mpr hp_lt
  have hq_mem : q ∈ range Q₀ := mem_range.mpr hq_lt
  have hpq_mem : (p,q) ∈ PQ := by
    exact mem_product.mpr ⟨hp_mem, hq_mem⟩

  -- Thue適用条件
  have hcond : 3 ≤ p ∧ 3 ≤ q := ⟨hp, hq⟩

  -- Sxy の取得
  have h_thue := thue_finite p q k hp hq
  let Sxy := Classical.choose h_thue
  have hSxy := Classical.choose_spec h_thue

  -- (x,y) ∈ Sxy
  have hxy_mem : (x,y) ∈ Sxy := hSxy x y h_eq

  -- image による持ち上げ
  have h_img :
    (x, y, p, q) ∈
      Sxy.image (fun xy => (xy.1, xy.2, p, q)) :=
    by
      apply mem_image.mpr
      exact ⟨(x,y), hxy_mem, rfl⟩

  -- biUnion に入る
  have :
    (x, y, p, q) ∈ S_total :=
    by
      apply mem_biUnion.mpr
      refine ⟨(p,q), hpq_mem, ?_⟩
      simp [S_total, hcond, Sxy] at h_img
      exact h_img

  exact this

end Pillai
