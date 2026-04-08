lemma log_factor_control
  (y : ℕ) (A : ℝ)
  (hy : 2 ≤ y) (hA : 0 < A) :
  ∃ c > 0,
    ∀ q ≥ 1,
      ((q : ℝ) * log y) ^ (-A)
        ≥ c * (q : ℝ) ^ (-A) :=
by
  have hy' : 1 < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide) hy)

  have hlog : 0 < log y := log_pos hy'

  -- ケース分岐を吸収する定数
  let c :=
    min 1 ((log y) ^ (-A))

  have hc_pos : 0 < c := by
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h2 : 0 < (log y) ^ (-A) := by
      positivity
    exact lt_min h1 h2

  refine ⟨c, hc_pos, ?_⟩
  intro q hq

  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.succ_le_iff.mp hq

  -- 展開
  have :
    ((q : ℝ) * log y) ^ (-A)
      = (log y) ^ (-A) * (q : ℝ) ^ (-A) := by
    have hpos : (0 : ℝ) < log y := hlog
    field_simp [pow_mul, mul_comm]

  -- min で押さえる
  have hmin :
    c ≤ (log y) ^ (-A) := by
    apply min_le_right

  -- 結論
  have :=
    mul_le_mul_of_nonneg_right hmin (by positivity : 0 ≤ (q : ℝ) ^ (-A))

  simpa [c, this] using this
